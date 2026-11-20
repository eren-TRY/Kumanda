package com.example.tvkumanda

import android.annotation.SuppressLint
import android.app.Activity
import android.content.res.ColorStateList
import android.graphics.Color
import android.graphics.Typeface
import android.graphics.drawable.GradientDrawable
import android.graphics.drawable.RippleDrawable
import android.os.Bundle
import android.util.TypedValue
import android.view.Gravity
import android.view.HapticFeedbackConstants
import android.view.View
import android.widget.Button
import android.widget.EditText
import android.widget.FrameLayout
import android.widget.LinearLayout
import android.widget.ScrollView
import android.widget.TextView
import org.bouncycastle.asn1.x500.X500Name
import org.bouncycastle.cert.jcajce.JcaX509CertificateConverter
import org.bouncycastle.cert.jcajce.JcaX509v3CertificateBuilder
import org.bouncycastle.operator.jcajce.JcaContentSignerBuilder
import java.io.ByteArrayOutputStream
import java.io.EOFException
import java.io.File
import java.math.BigInteger
import java.net.InetSocketAddress
import java.net.Socket
import java.security.KeyFactory
import java.security.KeyPairGenerator
import java.security.MessageDigest
import java.security.Principal
import java.security.PrivateKey
import java.security.cert.CertificateFactory
import java.security.cert.X509Certificate
import java.security.interfaces.RSAPublicKey
import java.security.spec.PKCS8EncodedKeySpec
import java.util.Date
import java.util.concurrent.Executors
import javax.net.ssl.KeyManager
import javax.net.ssl.SSLContext
import javax.net.ssl.SSLSocket
import javax.net.ssl.TrustManager
import javax.net.ssl.X509KeyManager
import javax.net.ssl.X509TrustManager

object Pb {
    private val EMPTY = ByteArray(0)

    fun varint(value: Long): ByteArray {
        var v = value
        val out = ByteArrayOutputStream()
        while (true) {
            if ((v and 0x7FL.inv()) == 0L) {
                out.write(v.toInt())
                break
            }
            out.write(((v and 0x7F) or 0x80).toInt())
            v = v ushr 7
        }
        return out.toByteArray()
    }

    private fun tag(field: Int, wire: Int) = varint(((field shl 3) or wire).toLong())
    fun int(field: Int, v: Int) = tag(field, 0) + varint(v.toLong())
    fun bytes(field: Int, b: ByteArray) = tag(field, 2) + varint(b.size.toLong()) + b
    fun str(field: Int, s: String) = bytes(field, s.toByteArray(Charsets.UTF_8))

    class Field(val num: Int, val number: Long, val data: ByteArray)

    fun parse(b: ByteArray): List<Field> {
        val out = ArrayList<Field>()
        var i = 0
        fun readVar(): Long {
            var r = 0L
            var shift = 0
            while (i < b.size) {
                val x = b[i++].toInt() and 0xFF
                r = r or ((x and 0x7F).toLong() shl shift)
                if ((x and 0x80) == 0) return r
                shift += 7
                if (shift > 63) break
            }
            return r
        }
        while (i < b.size) {
            val key = readVar().toInt()
            val num = key ushr 3
            if (num <= 0) break
            when (key and 7) {
                0 -> out.add(Field(num, readVar(), EMPTY))
                2 -> {
                    val len = readVar().toInt()
                    if (len < 0 || i + len > b.size) break
                    out.add(Field(num, 0, b.copyOfRange(i, i + len)))
                    i += len
                }
                1 -> {
                    if (i + 8 > b.size) break
                    i += 8
                }
                5 -> {
                    if (i + 4 > b.size) break
                    i += 4
                }
                else -> break
            }
        }
        return out
    }
}

class Identity(val key: PrivateKey, val cert: X509Certificate)

class Conn(val sock: SSLSocket) {
    private val inp = sock.inputStream
    private val out = sock.outputStream

    fun send(msg: ByteArray) {
        synchronized(out) {
            out.write(Pb.varint(msg.size.toLong()) + msg)
            out.flush()
        }
    }

    fun read(): ByteArray {
        var len = 0
        var shift = 0
        while (true) {
            val b = inp.read()
            if (b < 0) throw EOFException("Bağlantı kapandı")
            len = len or ((b and 0x7F) shl shift)
            if ((b and 0x80) == 0) break
            shift += 7
        }
        if (len < 0 || len > 1024 * 1024) throw IllegalStateException("Geçersiz paket boyutu: $len")
        val buf = ByteArray(len)
        var off = 0
        while (off < len) {
            val n = inp.read(buf, off, len - off)
            if (n < 0) throw EOFException("Bağlantı kapandı")
            off += n
        }
        return buf
    }

    fun close() {
        try { sock.close() } catch (_: Exception) {}
    }
}

private class FixedKm(val id: Identity) : X509KeyManager {
    override fun getClientAliases(keyType: String?, issuers: Array<Principal>?): Array<String> = arrayOf("c")
    override fun chooseClientAlias(keyType: Array<String>?, issuers: Array<Principal>?, socket: Socket?): String = "c"
    override fun getServerAliases(keyType: String?, issuers: Array<Principal>?): Array<String>? = null
    override fun chooseServerAlias(keyType: String?, issuers: Array<Principal>?, socket: Socket?): String? = null
    override fun getCertificateChain(alias: String?): Array<X509Certificate> = arrayOf(id.cert)
    override fun getPrivateKey(alias: String?): PrivateKey = id.key
}

private class TrustAll : X509TrustManager {
    override fun checkClientTrusted(chain: Array<out X509Certificate>?, authType: String?) {}
    override fun checkServerTrusted(chain: Array<out X509Certificate>?, authType: String?) {}
    override fun getAcceptedIssuers(): Array<X509Certificate> = arrayOf()
}

private fun BigInteger.unsigned(): ByteArray {
    val b = toByteArray()
    return if (b.size > 1 && b[0] == 0.toByte()) b.copyOfRange(1, b.size) else b
}

private fun hexToBytes(s: String): ByteArray {
    require(s.length % 2 == 0) { "Hex uzunluğu çift olmalı" }
    return ByteArray(s.length / 2) { idx ->
        s.substring(idx * 2, idx * 2 + 2).toInt(16).toByte()
    }
}

private enum class StatusState {
    DISCONNECTED,
    ENTER_IP,
    PAIRING_START,
    ENTER_CODE,
    PAIRING_FAILED,
    CODE_LENGTH,
    CODE_REJECTED,
    PAIRED_CONNECTING,
    CONNECTING,
    CONNECT_FAILED,
    CONNECTED,
    LOST,
    PAIR_RESET,
    SEND_FAILED
}

private data class ColorPalette(
    val name: String,
    val bg: Int,
    val card: Int,
    val surface: Int,
    val btn: Int,
    val btnStroke: Int,
    val accent: Int,
    val accentStroke: Int,
    val accentText: Int = Color.WHITE
)

private data class UiStrings(
    val tabRemote: String,
    val tabConnect: String,
    val tvIpTitle: String,
    val prefsTitle: String,
    val lookLangTitle: String,
    val codeHint: String,
    val confirm: String,
    val connect: String,
    val hapticOn: String,
    val hapticOff: String,
    val autoOn: String,
    val autoOff: String,
    val resetPair: String,
    val statusDisconnected: String,
    val statusEnterIpFirst: String,
    val statusPairingStart: String,
    val statusEnterCode: String,
    val statusPairingFailed: String,
    val statusCodeLength: String,
    val statusCodeRejected: String,
    val statusPairedConnecting: String,
    val statusConnecting: String,
    val statusConnectFailed: String,
    val statusConnected: String,
    val statusLost: String,
    val statusPairReset: String,
    val statusSendFailed: String
)

private val stringsByLang = mapOf(
    "tr" to UiStrings(
        tabRemote = "Kumanda",
        tabConnect = "Bağlantı",
        tvIpTitle = "TV IP Adresi",
        prefsTitle = "Tercihler",
        lookLangTitle = "Tema ve Dil",
        codeHint = "6 haneli kod",
        confirm = "Onayla",
        connect = "Bağlan",
        hapticOn = "Titreşim: Açık",
        hapticOff = "Titreşim: Kapalı",
        autoOn = "Oto Bağlan: Açık",
        autoOff = "Oto Bağlan: Kapalı",
        resetPair = "Eşleştirmeyi Sıfırla",
        statusDisconnected = "Bağlı değil",
        statusEnterIpFirst = "Önce TV'nin IP adresini yaz",
        statusPairingStart = "Eşleştirme başlıyor…",
        statusEnterCode = "TV'deki 6 haneli kodu yazıp Onayla'ya bas",
        statusPairingFailed = "Eşleştirme başarısız",
        statusCodeLength = "Kod 6 karakter olmalı",
        statusCodeRejected = "Kod kabul edilmedi",
        statusPairedConnecting = "Eşleşti — Bağlanıyor…",
        statusConnecting = "Bağlanıyor…",
        statusConnectFailed = "Bağlanamadı",
        statusConnected = "Bağlandı",
        statusLost = "Bağlantı koptu",
        statusPairReset = "Eşleştirme sıfırlandı",
        statusSendFailed = "Gönderilemedi"
    ),
    "en" to UiStrings(
        tabRemote = "Remote",
        tabConnect = "Connection",
        tvIpTitle = "TV IP Address",
        prefsTitle = "Preferences",
        lookLangTitle = "Theme & Language",
        codeHint = "6-digit code",
        confirm = "Confirm",
        connect = "Connect",
        hapticOn = "Haptic: On",
        hapticOff = "Haptic: Off",
        autoOn = "Auto Connect: On",
        autoOff = "Auto Connect: Off",
        resetPair = "Reset Pairing",
        statusDisconnected = "Disconnected",
        statusEnterIpFirst = "Enter the TV IP address first",
        statusPairingStart = "Starting pairing…",
        statusEnterCode = "Enter the 6-digit code on TV and tap Confirm",
        statusPairingFailed = "Pairing failed",
        statusCodeLength = "Code must be 6 characters",
        statusCodeRejected = "Code rejected",
        statusPairedConnecting = "Paired — Connecting…",
        statusConnecting = "Connecting…",
        statusConnectFailed = "Connection failed",
        statusConnected = "Connected",
        statusLost = "Connection lost",
        statusPairReset = "Pairing reset",
        statusSendFailed = "Failed to send"
    ),
    "ru" to UiStrings(
        tabRemote = "Пульт",
        tabConnect = "Подключение",
        tvIpTitle = "IP-адрес ТВ",
        prefsTitle = "Настройки",
        lookLangTitle = "Тема и язык",
        codeHint = "6-значный код",
        confirm = "ОК",
        connect = "Подключить",
        hapticOn = "Вибрация: Вкл",
        hapticOff = "Вибрация: Выкл",
        autoOn = "Автоподкл.: Вкл",
        autoOff = "Автоподкл.: Выкл",
        resetPair = "Сбросить пару",
        statusDisconnected = "Не подключено",
        statusEnterIpFirst = "Сначала введите IP-адрес ТВ",
        statusPairingStart = "Начинаем сопряжение…",
        statusEnterCode = "Введите 6-значный код с ТВ и нажмите ОК",
        statusPairingFailed = "Ошибка сопряжения",
        statusCodeLength = "Код должен быть из 6 символов",
        statusCodeRejected = "Код отклонён",
        statusPairedConnecting = "Сопряжено — Подключение…",
        statusConnecting = "Подключение…",
        statusConnectFailed = "Не удалось подключиться",
        statusConnected = "Подключено",
        statusLost = "Соединение потеряно",
        statusPairReset = "Сопряжение сброшено",
        statusSendFailed = "Ошибка отправки"
    ),
    "az" to UiStrings(
        tabRemote = "Pult",
        tabConnect = "Bağlantı",
        tvIpTitle = "TV IP Ünvanı",
        prefsTitle = "Tənzimləmələr",
        lookLangTitle = "Mövzu və Dil",
        codeHint = "6 rəqəmli kod",
        confirm = "Təsdiqlə",
        connect = "Qoşul",
        hapticOn = "Titrəmə: Açıq",
        hapticOff = "Titrəmə: Bağlı",
        autoOn = "Avto Qoşul: Açıq",
        autoOff = "Avto Qoşul: Bağlı",
        resetPair = "Cütləşməni Sıfırla",
        statusDisconnected = "Qoşulu deyil",
        statusEnterIpFirst = "Əvvəlcə TV-nin IP ünvanını yaz",
        statusPairingStart = "Cütləşmə başlayır…",
        statusEnterCode = "TV-dəki 6 rəqəmli kodu yazıb Təsdiqlə bas",
        statusPairingFailed = "Cütləşmə uğursuz oldu",
        statusCodeLength = "Kod 6 simvol olmalıdır",
        statusCodeRejected = "Kod qəbul edilmədi",
        statusPairedConnecting = "Cütləşdi — Qoşulur…",
        statusConnecting = "Qoşulur…",
        statusConnectFailed = "Qoşulmaq olmadı",
        statusConnected = "Qoşuldu",
        statusLost = "Bağlantı kəsildi",
        statusPairReset = "Cütləşmə sıfırlandı",
        statusSendFailed = "Göndərilə bilmədi"
    )
)

class MainActivity : Activity() {

    private val fastIo = Executors.newCachedThreadPool()
    private var identity: Identity? = null
    private var remote: Conn? = null
    @Volatile private var ready = false
    @Volatile private var reconnecting = false
    private var pairConn: Conn? = null
    private var pairServerCert: X509Certificate? = null
    private var host = ""
    @Volatile private var hapticEnabled = true
    @Volatile private var autoConnectEnabled = true
    private var currentLang = "tr"
    private var lastStatusState = StatusState.DISCONNECTED
    private var lastStatusDetail: String? = null
    private var lastStatusDotColor = Color.parseColor("#64748B")

    private val palettes = listOf(
        ColorPalette(
            name = "Mavi",
            bg = Color.parseColor("#0B0D12"),
            card = Color.parseColor("#141821"),
            surface = Color.parseColor("#10141C"),
            btn = Color.parseColor("#1D222E"),
            btnStroke = Color.parseColor("#2B3242"),
            accent = Color.parseColor("#2563EB"),
            accentStroke = Color.parseColor("#60A5FA")
        ),
        ColorPalette(
            name = "Zümrüt",
            bg = Color.parseColor("#09110E"),
            card = Color.parseColor("#111F1A"),
            surface = Color.parseColor("#0D1814"),
            btn = Color.parseColor("#182B24"),
            btnStroke = Color.parseColor("#264237"),
            accent = Color.parseColor("#059669"),
            accentStroke = Color.parseColor("#34D399")
        ),
        ColorPalette(
            name = "Mor",
            bg = Color.parseColor("#0E0B14"),
            card = Color.parseColor("#191424"),
            surface = Color.parseColor("#13101C"),
            btn = Color.parseColor("#241D33"),
            btnStroke = Color.parseColor("#362C4D"),
            accent = Color.parseColor("#7C3AED"),
            accentStroke = Color.parseColor("#A78BFA")
        ),
        ColorPalette(
            name = "Kehribar",
            bg = Color.parseColor("#120E09"),
            card = Color.parseColor("#201810"),
            surface = Color.parseColor("#18120C"),
            btn = Color.parseColor("#2E2216"),
            btnStroke = Color.parseColor("#453321"),
            accent = Color.parseColor("#D97706"),
            accentStroke = Color.parseColor("#FBBF24")
        ),
        ColorPalette(
            name = "Siyah Beyaz",
            bg = Color.parseColor("#000000"),
            card = Color.parseColor("#121212"),
            surface = Color.parseColor("#0A0A0A"),
            btn = Color.parseColor("#1E1E1E"),
            btnStroke = Color.parseColor("#4A4A4A"),
            accent = Color.parseColor("#FFFFFF"),
            accentStroke = Color.parseColor("#FFFFFF"),
            accentText = Color.parseColor("#000000")
        )
    )

    private var paletteIndex = 0
    private var cBg = palettes[0].bg
    private var cCard = palettes[0].card
    private var cSurface = palettes[0].surface
    private var cBtn = palettes[0].btn
    private var cBtnStroke = palettes[0].btnStroke
    private var cAccent = palettes[0].accent
    private var cAccentStroke = palettes[0].accentStroke
    private var cAccentText = palettes[0].accentText

    private val cRedSoft = Color.parseColor("#2A1418")
    private val cRedStroke = Color.parseColor("#F87171")
    private val cGreen = Color.parseColor("#22C55E")
    private val cMuted = Color.parseColor("#64748B")
    private val cText = Color.parseColor("#F8FAFC")
    private val cSubtext = Color.parseColor("#CBD5E1")

    private lateinit var rootView: LinearLayout
    private lateinit var topBarView: LinearLayout
    private lateinit var dpadClusterView: LinearLayout
    private lateinit var connectCardView: LinearLayout
    private lateinit var prefsCardView: LinearLayout
    private lateinit var lookCardView: LinearLayout
    private lateinit var tvIpTitleView: TextView
    private lateinit var prefsTitleView: TextView
    private lateinit var lookLangTitleView: TextView
    private lateinit var connectBtnView: Button
    private lateinit var resetPairBtnView: Button
    private lateinit var confirmPairBtnView: Button
    private lateinit var okBtnView: Button
    private lateinit var statusDot: View
    private lateinit var status: TextView
    private lateinit var ipBox: EditText
    private lateinit var codeBox: EditText
    private lateinit var codeRow: LinearLayout
    private lateinit var hapticBtn: Button
    private lateinit var autoConnectBtn: Button

    private var dp = 1f
    private var sp = 1f
    private var currentScreen = 0
    private val navBtns = ArrayList<Button>()
    private val neutralPillBtns = ArrayList<Button>()
    private val circleBtns = ArrayList<Button>()
    private val paletteBtns = ArrayList<Button>()
    private val langBtns = ArrayList<Pair<String, Button>>()
    private val screens = ArrayList<View>()

    private fun strings(): UiStrings = stringsByLang[currentLang] ?: stringsByLang.getValue("tr")
    private fun px(v: Int) = (v * dp).toInt()
    private fun scaledSp(v: Float) = v * (sp / dp).coerceIn(0.85f, 1.3f)

    private fun tap(type: Int = HapticFeedbackConstants.VIRTUAL_KEY, v: View? = null) {
        if (hapticEnabled) {
            v?.performHapticFeedback(type) ?: window.decorView.performHapticFeedback(type)
        }
    }

    private fun remoteScreen(vararg rows: View) = LinearLayout(this).apply {
        orientation = LinearLayout.VERTICAL
        gravity = Gravity.CENTER_HORIZONTAL
        visibility = View.GONE
        setPadding(px(14), px(6), px(14), px(8))
        rows.forEachIndexed { idx, r ->
            val lp = when (idx) {
                0 -> LinearLayout.LayoutParams(
                    LinearLayout.LayoutParams.MATCH_PARENT, px(54)
                ).apply { setMargins(0, px(2), 0, px(8)) }
                1 -> LinearLayout.LayoutParams(
                    LinearLayout.LayoutParams.MATCH_PARENT, px(56)
                ).apply { setMargins(0, px(2), 0, px(12)) }
                2 -> LinearLayout.LayoutParams(
                    LinearLayout.LayoutParams.MATCH_PARENT, 0, 1f
                ).apply { setMargins(0, px(2), 0, px(12)) }
                else -> LinearLayout.LayoutParams(
                    LinearLayout.LayoutParams.MATCH_PARENT, px(56)
                ).apply { setMargins(0, px(2), 0, px(2)) }
            }
            r.layoutParams = lp
            addView(r)
        }
        screens.add(this)
    }

    private fun scrollFormScreen(vararg cards: View) = ScrollView(this).apply {
        visibility = View.GONE
        isFillViewport = true
        overScrollMode = View.OVER_SCROLL_NEVER
        setPadding(px(14), px(8), px(14), px(12))
        addView(
            LinearLayout(this@MainActivity).apply {
                orientation = LinearLayout.VERTICAL
                gravity = Gravity.CENTER_HORIZONTAL
                layoutParams = LinearLayout.LayoutParams(
                    LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT
                )
                cards.forEachIndexed { i, c ->
                    val lp = LinearLayout.LayoutParams(
                        LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT
                    ).apply {
                        if (i > 0) setMargins(0, px(12), 0, 0)
                    }
                    c.layoutParams = lp
                    addView(c)
                }
            }
        )
        screens.add(this)
    }

    private fun show(i: Int) {
        currentScreen = i
        screens.forEachIndexed { n, sc -> sc.visibility = if (n == i) View.VISIBLE else View.GONE }
        navBtns.forEachIndexed { n, b ->
            val active = n == i
            b.background = makePillBg(if (active) cAccent else cCard, if (active) cAccentStroke else cBtnStroke)
            b.setTextColor(if (active) cAccentText else cSubtext)
        }
    }

    private fun nav(label: String, i: Int) = Button(this).apply {
        text = label
        setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(14f))
        typeface = Typeface.DEFAULT_BOLD
        isAllCaps = false
        setPadding(px(6), px(2), px(6), px(2))
        layoutParams = LinearLayout.LayoutParams(0, px(54), 1f).apply {
            setMargins(px(5), px(2), px(5), px(4))
        }
        navBtns.add(this)
        setOnClickListener {
            tap(HapticFeedbackConstants.KEYBOARD_TAP, this)
            show(i)
        }
    }

    private fun makeCircleBg(fill: Int, stroke: Int): RippleDrawable {
        val shape = GradientDrawable().apply {
            shape = GradientDrawable.OVAL
            setColor(fill)
            setStroke(px(1.5.toInt()), stroke)
        }
        return RippleDrawable(ColorStateList.valueOf(Color.parseColor("#38FFFFFF")), shape, null)
    }

    private fun makePillBg(fill: Int, stroke: Int, radiusDp: Int = 22): RippleDrawable {
        val shape = GradientDrawable().apply {
            shape = GradientDrawable.RECTANGLE
            cornerRadius = px(radiusDp).toFloat()
            setColor(fill)
            setStroke(px(1.5.toInt()), stroke)
        }
        return RippleDrawable(ColorStateList.valueOf(Color.parseColor("#38FFFFFF")), shape, null)
    }

    private fun makeClusterBg(): GradientDrawable = GradientDrawable().apply {
        shape = GradientDrawable.RECTANGLE
        cornerRadius = px(28).toFloat()
        setColor(cSurface)
        setStroke(px(1), cBtnStroke)
    }

    private fun makeInputBg(): GradientDrawable = GradientDrawable().apply {
        cornerRadius = px(18).toFloat()
        setColor(cCard)
        setStroke(px(1), cBtnStroke)
    }

    private fun formatStatus(state: StatusState, detail: String?): String {
        val s = strings()
        val base = when (state) {
            StatusState.DISCONNECTED -> s.statusDisconnected
            StatusState.ENTER_IP -> s.statusEnterIpFirst
            StatusState.PAIRING_START -> s.statusPairingStart
            StatusState.ENTER_CODE -> s.statusEnterCode
            StatusState.PAIRING_FAILED -> s.statusPairingFailed
            StatusState.CODE_LENGTH -> s.statusCodeLength
            StatusState.CODE_REJECTED -> s.statusCodeRejected
            StatusState.PAIRED_CONNECTING -> s.statusPairedConnecting
            StatusState.CONNECTING -> s.statusConnecting
            StatusState.CONNECT_FAILED -> s.statusConnectFailed
            StatusState.CONNECTED -> s.statusConnected
            StatusState.LOST -> s.statusLost
            StatusState.PAIR_RESET -> s.statusPairReset
            StatusState.SEND_FAILED -> s.statusSendFailed
        }
        return if (!detail.isNullOrBlank()) "$base: $detail" else base
    }

    private fun applyLanguage(lang: String) {
        currentLang = if (stringsByLang.containsKey(lang)) lang else "tr"
        val s = strings()
        if (navBtns.size >= 2) {
            navBtns[0].text = s.tabRemote
            navBtns[1].text = s.tabConnect
        }
        tvIpTitleView.text = s.tvIpTitle
        prefsTitleView.text = s.prefsTitle
        lookLangTitleView.text = s.lookLangTitle
        codeBox.hint = s.codeHint
        confirmPairBtnView.text = s.confirm
        connectBtnView.text = s.connect
        hapticBtn.text = if (hapticEnabled) s.hapticOn else s.hapticOff
        autoConnectBtn.text = if (autoConnectEnabled) s.autoOn else s.autoOff
        resetPairBtnView.text = s.resetPair

        status.text = formatStatus(lastStatusState, lastStatusDetail)
        (statusDot.background as? GradientDrawable)?.setColor(lastStatusDotColor)

        langBtns.forEach { (code, b) ->
            val selected = code == currentLang
            b.background = makePillBg(
                if (selected) cAccent else cBtn,
                if (selected) cAccentStroke else cBtnStroke,
                radiusDp = 16
            )
            b.setTextColor(if (selected) cAccentText else cSubtext)
        }
    }

    private fun applyPalette(index: Int) {
        val p = palettes[index.coerceIn(0, palettes.lastIndex)]
        paletteIndex = index
        cBg = p.bg
        cCard = p.card
        cSurface = p.surface
        cBtn = p.btn
        cBtnStroke = p.btnStroke
        cAccent = p.accent
        cAccentStroke = p.accentStroke
        cAccentText = p.accentText

        rootView.setBackgroundColor(cBg)
        topBarView.background = GradientDrawable().apply {
            cornerRadius = px(20).toFloat()
            setColor(cCard)
            setStroke(px(1), cBtnStroke)
        }
        dpadClusterView.background = makeClusterBg()
        connectCardView.background = makeClusterBg()
        prefsCardView.background = makeClusterBg()
        lookCardView.background = makeClusterBg()

        ipBox.background = makeInputBg()
        codeBox.background = makeInputBg()

        neutralPillBtns.forEach { b ->
            b.background = makePillBg(cBtn, cBtnStroke)
            b.setTextColor(cText)
        }
        circleBtns.forEach { b ->
            b.background = makeCircleBg(cBtn, cBtnStroke)
            b.setTextColor(cText)
        }
        okBtnView.background = makeCircleBg(cAccent, cAccentStroke)
        okBtnView.setTextColor(cAccentText)

        connectBtnView.background = makePillBg(cAccent, cAccentStroke, radiusDp = 18)
        connectBtnView.setTextColor(cAccentText)

        confirmPairBtnView.background = makePillBg(cAccent, cAccentStroke, radiusDp = 18)
        confirmPairBtnView.setTextColor(cAccentText)

        resetPairBtnView.background = makePillBg(cRedSoft, cRedStroke, radiusDp = 16)

        hapticBtn.background = makePillBg(if (hapticEnabled) cBtn else cCard, cBtnStroke, radiusDp = 16)
        hapticBtn.setTextColor(if (hapticEnabled) cText else cSubtext)

        autoConnectBtn.background = makePillBg(if (autoConnectEnabled) cBtn else cCard, cBtnStroke, radiusDp = 16)
        autoConnectBtn.setTextColor(if (autoConnectEnabled) cText else cSubtext)

        paletteBtns.forEachIndexed { idx, b ->
            val selected = idx == paletteIndex
            val item = palettes[idx]
            b.background = makePillBg(
                if (selected) item.accent else cBtn,
                if (selected) item.accentStroke else cBtnStroke,
                radiusDp = 16
            )
            b.setTextColor(if (selected) item.accentText else cSubtext)
        }

        applyLanguage(currentLang)
        show(currentScreen)
    }

    @SuppressLint("ClickableViewAccessibility")
    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        dp = resources.displayMetrics.density
        sp = resources.displayMetrics.scaledDensity
        val prefs = getSharedPreferences("tv", MODE_PRIVATE)
        val paired = prefs.getBoolean("paired", false)
        hapticEnabled = prefs.getBoolean("haptic", true)
        autoConnectEnabled = prefs.getBoolean("auto_connect", true)
        paletteIndex = prefs.getInt("palette", 0).coerceIn(0, palettes.lastIndex)
        currentLang = prefs.getString("lang", "tr") ?: "tr"
        lastStatusState = if (paired) StatusState.DISCONNECTED else StatusState.ENTER_IP
        lastStatusDotColor = cMuted
        val s = strings()

        ipBox = EditText(this).apply {
            hint = "192.168.1.105"
            setHintTextColor(cMuted)
            setTextColor(cText)
            typeface = Typeface.DEFAULT_BOLD
            setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(17f))
            background = makeInputBg()
            setPadding(px(18), px(15), px(18), px(15))
            setText(prefs.getString("ip", ""))
            setSingleLine()
            layoutParams = LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT
            ).apply { setMargins(0, 0, 0, px(12)) }
        }
        codeBox = EditText(this).apply {
            hint = s.codeHint
            setHintTextColor(cMuted)
            setTextColor(cText)
            typeface = Typeface.DEFAULT_BOLD
            setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(16f))
            background = makeInputBg()
            setPadding(px(16), px(14), px(16), px(14))
            setSingleLine()
            layoutParams = LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f).apply {
                setMargins(0, 0, px(10), 0)
            }
        }
        confirmPairBtnView = Button(this).apply {
            text = s.confirm
            stylePill(this, cAccent, cAccentStroke, 15f, radiusDp = 18)
            layoutParams = LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.WRAP_CONTENT, px(52)
            )
            setOnClickListener {
                tap(HapticFeedbackConstants.KEYBOARD_TAP, this)
                finishPairing(codeBox.text.toString())
            }
        }
        codeRow = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER_VERTICAL
            visibility = View.GONE
            setPadding(0, px(12), 0, 0)
            addView(codeBox)
            addView(confirmPairBtnView)
        }
        statusDot = View(this).apply {
            layoutParams = LinearLayout.LayoutParams(px(10), px(10)).apply {
                setMargins(0, 0, px(10), 0)
            }
            background = GradientDrawable().apply {
                shape = GradientDrawable.OVAL
                setColor(cMuted)
            }
        }
        status = TextView(this).apply {
            text = formatStatus(lastStatusState, null)
            setTextColor(cSubtext)
            setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(13.5f))
            setSingleLine()
        }

        okBtnView = squareKey("OK", 23, cAccent, cAccentStroke, sizeDp = 84, sizeSp = 18f, trackCircle = false)

        dpadClusterView = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            gravity = Gravity.CENTER
            background = makeClusterBg()
            setPadding(px(12), px(14), px(12), px(14))
            addView(
                row(
                    gap(1f),
                    squareKey("▲", 19, sizeDp = 72, sizeSp = 22f),
                    gap(1f)
                ).apply {
                    layoutParams = LinearLayout.LayoutParams(
                        LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT
                    ).apply { setMargins(0, 0, 0, px(6)) }
                }
            )
            addView(
                row(
                    squareKey("◀", 21, sizeDp = 72, sizeSp = 22f),
                    okBtnView,
                    squareKey("▶", 22, sizeDp = 72, sizeSp = 22f)
                ).apply {
                    layoutParams = LinearLayout.LayoutParams(
                        LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT
                    ).apply { setMargins(0, px(2), 0, px(6)) }
                }
            )
            addView(
                row(
                    gap(1f),
                    squareKey("▼", 20, sizeDp = 72, sizeSp = 22f),
                    gap(1f)
                ).apply {
                    layoutParams = LinearLayout.LayoutParams(
                        LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT
                    )
                }
            )
        }

        remoteScreen(
            row(
                gap(1.4f),
                pillKey("⏻", 26, cRedSoft, cRedStroke, weight = 0.9f, sizeSp = 20f, trackNeutral = false)
            ),
            row(
                pillKey("🔊+", 24, weight = 1.15f, sizeSp = 17.5f),
                pillKey("🔇", 164, weight = 0.9f, sizeSp = 17.5f),
                pillKey("🔊−", 25, weight = 1.15f, sizeSp = 17.5f)
            ),
            dpadClusterView,
            row(
                pillKey("↩", 4, weight = 1f, sizeSp = 19f),
                pillKey("⌂", 3, weight = 1f, sizeSp = 19f),
                pillKey("⚙", 176, weight = 1f, sizeSp = 19f)
            )
        )

        connectBtnView = Button(this).apply {
            text = s.connect
            stylePill(this, cAccent, cAccentStroke, 16f, radiusDp = 18)
            layoutParams = LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT, px(54)
            )
            setOnClickListener {
                tap(HapticFeedbackConstants.KEYBOARD_TAP, this)
                val cleanIp = ipBox.text.toString().trim()
                prefs.edit().putString("ip", cleanIp).apply()
                if (prefs.getBoolean("paired", false)) {
                    connectClicked()
                } else {
                    startPairing()
                }
            }
        }

        tvIpTitleView = TextView(this).apply {
            text = s.tvIpTitle
            setTextColor(cText)
            typeface = Typeface.DEFAULT_BOLD
            setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(17.5f))
            setPadding(px(2), 0, 0, px(10))
        }

        connectCardView = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            background = makeClusterBg()
            setPadding(px(16), px(16), px(16), px(16))
            addView(tvIpTitleView)
            addView(ipBox)
            addView(connectBtnView)
            addView(codeRow)
        }

        hapticBtn = Button(this).apply {
            text = if (hapticEnabled) s.hapticOn else s.hapticOff
            stylePill(this, if (hapticEnabled) cBtn else cCard, cBtnStroke, 14f, radiusDp = 16)
            layoutParams = LinearLayout.LayoutParams(0, px(48), 1f).apply {
                setMargins(0, 0, px(6), 0)
            }
            setOnClickListener {
                hapticEnabled = !hapticEnabled
                prefs.edit().putBoolean("haptic", hapticEnabled).apply()
                val cur = strings()
                text = if (hapticEnabled) cur.hapticOn else cur.hapticOff
                background = makePillBg(if (hapticEnabled) cBtn else cCard, cBtnStroke, radiusDp = 16)
                setTextColor(if (hapticEnabled) cText else cSubtext)
                tap(HapticFeedbackConstants.KEYBOARD_TAP, this)
            }
        }

        autoConnectBtn = Button(this).apply {
            text = if (autoConnectEnabled) s.autoOn else s.autoOff
            stylePill(this, if (autoConnectEnabled) cBtn else cCard, cBtnStroke, 14f, radiusDp = 16)
            layoutParams = LinearLayout.LayoutParams(0, px(48), 1f).apply {
                setMargins(px(6), 0, 0, 0)
            }
            setOnClickListener {
                tap(HapticFeedbackConstants.KEYBOARD_TAP, this)
                autoConnectEnabled = !autoConnectEnabled
                prefs.edit().putBoolean("auto_connect", autoConnectEnabled).apply()
                val cur = strings()
                text = if (autoConnectEnabled) cur.autoOn else cur.autoOff
                background = makePillBg(if (autoConnectEnabled) cBtn else cCard, cBtnStroke, radiusDp = 16)
                setTextColor(if (autoConnectEnabled) cText else cSubtext)
            }
        }

        resetPairBtnView = Button(this).apply {
            text = s.resetPair
            stylePill(this, cRedSoft, cRedStroke, 14f, radiusDp = 16)
            layoutParams = LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT, px(46)
            ).apply { setMargins(0, px(10), 0, 0) }
            setOnClickListener {
                tap(HapticFeedbackConstants.KEYBOARD_TAP, this)
                prefs.edit().putBoolean("paired", false).apply()
                pairConn?.close()
                pairConn = null
                remote?.close()
                remote = null
                ready = false
                codeRow.visibility = View.GONE
                uiState(StatusState.PAIR_RESET, cMuted)
            }
        }

        prefsTitleView = TextView(this).apply {
            text = s.prefsTitle
            setTextColor(cText)
            typeface = Typeface.DEFAULT_BOLD
            setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(16.5f))
            setPadding(px(2), 0, 0, px(10))
        }

        prefsCardView = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            background = makeClusterBg()
            setPadding(px(16), px(16), px(16), px(16))
            addView(prefsTitleView)
            addView(
                row(hapticBtn, autoConnectBtn).apply {
                    layoutParams = LinearLayout.LayoutParams(
                        LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT
                    )
                }
            )
            addView(resetPairBtnView)
        }

        val paletteRow1 = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER
            layoutParams = LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT
            ).apply { setMargins(0, 0, 0, px(8)) }
        }
        val paletteRow2 = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER
            layoutParams = LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT
            ).apply { setMargins(0, 0, 0, px(8)) }
        }
        val paletteRow3 = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER
            layoutParams = LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT
            ).apply { setMargins(0, 0, 0, px(12)) }
        }

        palettes.forEachIndexed { idx, p ->
            val pb = Button(this).apply {
                text = p.name
                stylePill(this, cBtn, cBtnStroke, 13.5f, radiusDp = 16)
                layoutParams = LinearLayout.LayoutParams(0, px(44), 1f).apply {
                    if (idx < 4) {
                        val isLeft = (idx % 2 == 0)
                        setMargins(if (isLeft) 0 else px(5), 0, if (isLeft) px(5) else 0, 0)
                    } else {
                        setMargins(0, 0, 0, 0)
                    }
                }
                setOnClickListener {
                    tap(HapticFeedbackConstants.KEYBOARD_TAP, this)
                    prefs.edit().putInt("palette", idx).apply()
                    applyPalette(idx)
                }
            }
            paletteBtns.add(pb)
            when {
                idx < 2 -> paletteRow1.addView(pb)
                idx < 4 -> paletteRow2.addView(pb)
                else -> paletteRow3.addView(pb)
            }
        }

        val langOptions = listOf(
            "tr" to "Türkçe",
            "en" to "English",
            "ru" to "Русский",
            "az" to "Azərbaycan"
        )
        val langRow1 = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER
            layoutParams = LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT
            ).apply { setMargins(0, 0, 0, px(8)) }
        }
        val langRow2 = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER
            layoutParams = LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT
            )
        }

        langOptions.forEachIndexed { idx, (code, label) ->
            val lb = Button(this).apply {
                text = label
                stylePill(this, cBtn, cBtnStroke, 13.5f, radiusDp = 16)
                val isLeft = (idx % 2 == 0)
                layoutParams = LinearLayout.LayoutParams(0, px(44), 1f).apply {
                    setMargins(if (isLeft) 0 else px(5), 0, if (isLeft) px(5) else 0, 0)
                }
                setOnClickListener {
                    tap(HapticFeedbackConstants.KEYBOARD_TAP, this)
                    prefs.edit().putString("lang", code).apply()
                    applyLanguage(code)
                }
            }
            langBtns.add(code to lb)
            if (idx < 2) langRow1.addView(lb) else langRow2.addView(lb)
        }

        lookLangTitleView = TextView(this).apply {
            text = s.lookLangTitle
            setTextColor(cText)
            typeface = Typeface.DEFAULT_BOLD
            setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(16.5f))
            setPadding(px(2), 0, 0, px(10))
        }

        lookCardView = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            background = makeClusterBg()
            setPadding(px(16), px(16), px(16), px(16))
            addView(lookLangTitleView)
            addView(paletteRow1)
            addView(paletteRow2)
            addView(paletteRow3)
            addView(langRow1)
            addView(langRow2)
        }

        scrollFormScreen(connectCardView, prefsCardView, lookCardView)

        topBarView = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER_VERTICAL
            background = GradientDrawable().apply {
                cornerRadius = px(20).toFloat()
                setColor(cCard)
                setStroke(px(1), cBtnStroke)
            }
            setPadding(px(16), px(11), px(16), px(11))
            layoutParams = LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT
            ).apply { setMargins(px(14), px(2), px(14), px(6)) }
            addView(statusDot)
            addView(status)
        }

        val content = FrameLayout(this).apply {
            layoutParams = LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT, 0, 1f
            )
            screens.forEach {
                addView(it, FrameLayout.LayoutParams(
                    FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.MATCH_PARENT
                ))
            }
        }

        val bottomNav = row(nav(s.tabRemote, 0), nav(s.tabConnect, 1)).apply {
            setPadding(px(8), px(2), px(8), px(4))
        }

        rootView = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setBackgroundColor(cBg)
            setPadding(px(4), px(26), px(4), px(6))
            addView(topBarView)
            addView(content)
            addView(bottomNav)
        }
        setContentView(rootView)

        applyPalette(paletteIndex)

        if (paired && ipBox.text.isNotBlank()) {
            show(0)
            if (autoConnectEnabled) {
                connectClicked()
            }
        } else {
            show(1)
        }
    }

    private fun fillLp(weight: Float = 1f) = LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.MATCH_PARENT, weight).apply {
        setMargins(px(5), 0, px(5), 0)
    }

    private fun squareLp(sizeDp: Int) = LinearLayout.LayoutParams(px(sizeDp), px(sizeDp)).apply {
        setMargins(px(8), px(2), px(8), px(2))
    }

    private fun stylePill(b: Button, fill: Int, stroke: Int, sizeSp: Float, radiusDp: Int = 22) {
        b.background = makePillBg(fill, stroke, radiusDp = radiusDp)
        b.setTextColor(cText)
        b.typeface = Typeface.DEFAULT_BOLD
        b.isAllCaps = false
        b.setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(sizeSp))
        b.setPadding(px(6), 0, px(6), 0)
        b.minWidth = 0
        b.minimumWidth = 0
        b.minHeight = 0
        b.minimumHeight = 0
    }

    private fun styleCircle(b: Button, fill: Int, stroke: Int, sizeSp: Float) {
        b.background = makeCircleBg(fill, stroke)
        b.setTextColor(cText)
        b.typeface = Typeface.DEFAULT_BOLD
        b.isAllCaps = false
        b.setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(sizeSp))
        b.setPadding(0, 0, 0, 0)
        b.minWidth = 0
        b.minimumWidth = 0
        b.minHeight = 0
        b.minimumHeight = 0
    }

    private fun row(vararg views: View) = LinearLayout(this).apply {
        orientation = LinearLayout.HORIZONTAL
        gravity = Gravity.CENTER
        views.forEach { addView(it) }
    }

    private fun pillKey(
        label: String,
        code: Int,
        fill: Int = cBtn,
        stroke: Int = cBtnStroke,
        weight: Float = 1f,
        sizeSp: Float = 17f,
        trackNeutral: Boolean = true
    ) = Button(this).apply {
        text = label
        stylePill(this, fill, stroke, sizeSp)
        layoutParams = fillLp(weight)
        if (trackNeutral) neutralPillBtns.add(this)
        setOnClickListener {
            tap(HapticFeedbackConstants.VIRTUAL_KEY, this)
            sendKey(code)
        }
    }

    private fun squareKey(
        label: String,
        code: Int,
        fill: Int = cBtn,
        stroke: Int = cBtnStroke,
        sizeDp: Int = 72,
        sizeSp: Float = 22f,
        trackCircle: Boolean = true
    ) = Button(this).apply {
        text = label
        styleCircle(this, fill, stroke, sizeSp)
        layoutParams = squareLp(sizeDp)
        if (trackCircle) circleBtns.add(this)
        setOnClickListener {
            tap(HapticFeedbackConstants.VIRTUAL_KEY, this)
            sendKey(code)
        }
    }

    private fun gap(weight: Float = 1f) = View(this).apply {
        layoutParams = LinearLayout.LayoutParams(0, px(1), weight)
    }

    private fun uiState(state: StatusState, dotColor: Int, detail: String? = null) = runOnUiThread {
        lastStatusState = state
        lastStatusDetail = detail
        lastStatusDotColor = dotColor
        status.text = formatStatus(state, detail)
        (statusDot.background as? GradientDrawable)?.setColor(dotColor)
    }

    private fun identity(): Identity {
        identity?.let { return it }
        val kf = File(filesDir, "client.key")
        val cf = File(filesDir, "client.crt")
        val id: Identity
        if (kf.exists() && cf.exists()) {
            val key = KeyFactory.getInstance("RSA").generatePrivate(PKCS8EncodedKeySpec(kf.readBytes()))
            val cert = CertificateFactory.getInstance("X.509")
                .generateCertificate(cf.inputStream()) as X509Certificate
            id = Identity(key, cert)
        } else {
            val kpg = KeyPairGenerator.getInstance("RSA")
            kpg.initialize(2048)
            val kp = kpg.generateKeyPair()
            val name = X500Name("CN=atvremote")
            val now = Date()
            val builder = JcaX509v3CertificateBuilder(
                name,
                BigInteger.valueOf(System.currentTimeMillis()),
                now,
                Date(now.time + 20L * 365L * 24L * 3600L * 1000L),
                name,
                kp.public
            )
            val signer = JcaContentSignerBuilder("SHA256withRSA").build(kp.private)
            val cert = JcaX509CertificateConverter().getCertificate(builder.build(signer))
            kf.writeBytes(kp.private.encoded)
            cf.writeBytes(cert.encoded)
            id = Identity(kp.private, cert)
        }
        identity = id
        return id
    }

    private fun openTls(h: String, port: Int, id: Identity, readTimeoutMs: Int): Conn {
        val ctx = SSLContext.getInstance("TLS")
        ctx.init(arrayOf<KeyManager>(FixedKm(id)), arrayOf<TrustManager>(TrustAll()), null)
        val s = ctx.socketFactory.createSocket() as SSLSocket
        s.connect(InetSocketAddress(h, port), 2000)
        s.tcpNoDelay = true
        s.soTimeout = readTimeoutMs
        s.startHandshake()
        return Conn(s)
    }

    private fun outer(field: Int, inner: ByteArray) =
        Pb.int(1, 2) + Pb.int(2, 200) + Pb.bytes(field, inner)

    private fun expect(c: Conn, field: Int) {
        while (true) {
            val m = Pb.parse(c.read())
            val st = m.firstOrNull { it.num == 2 }?.number
            if (st != null && st != 200L) throw IllegalStateException("TV eşleştirmeyi reddetti ($st)")
            if (m.any { it.num == field }) return
        }
    }

    private fun startPairing() {
        val h = ipBox.text.toString().trim()
        if (h.isEmpty()) {
            uiState(StatusState.ENTER_IP, cRedStroke)
            return
        }
        host = h
        uiState(StatusState.PAIRING_START, cAccentStroke)
        fastIo.execute {
            try {
                pairConn?.close()
                val id = identity()
                val c = openTls(h, 6467, id, 10000)
                pairServerCert = c.sock.session.peerCertificates[0] as X509Certificate

                c.send(outer(10, Pb.str(1, "atvremote") + Pb.str(2, "TV Kumanda")))
                expect(c, 11)
                c.send(outer(20, Pb.bytes(1, Pb.int(1, 3) + Pb.int(2, 6)) + Pb.int(3, 1)))
                expect(c, 20)
                c.send(outer(30, Pb.bytes(1, Pb.int(1, 3) + Pb.int(2, 6)) + Pb.int(2, 1)))
                expect(c, 31)

                pairConn = c
                runOnUiThread { codeRow.visibility = View.VISIBLE }
                uiState(StatusState.ENTER_CODE, cAccentStroke)
            } catch (e: Exception) {
                uiState(StatusState.PAIRING_FAILED, cRedStroke, e.message)
            }
        }
    }

    private fun finishPairing(raw: String) {
        val code = raw.trim().uppercase()
        if (code.length != 6) {
            uiState(StatusState.CODE_LENGTH, cRedStroke)
            return
        }
        fastIo.execute {
            try {
                val c = pairConn ?: throw IllegalStateException(strings().connect)
                val serverCert = pairServerCert ?: throw IllegalStateException("Cert")
                val id = identity()
                val clientPub = id.cert.publicKey as RSAPublicKey
                val serverPub = serverCert.publicKey as RSAPublicKey
                val md = MessageDigest.getInstance("SHA-256")
                md.update(clientPub.modulus.unsigned())
                md.update(clientPub.publicExponent.unsigned())
                md.update(serverPub.modulus.unsigned())
                md.update(serverPub.publicExponent.unsigned())
                md.update(hexToBytes(code.substring(2)))
                val secret = md.digest()

                c.send(outer(40, Pb.bytes(1, secret)))
                expect(c, 41)
                c.close()
                pairConn = null

                getSharedPreferences("tv", MODE_PRIVATE).edit().putBoolean("paired", true).apply()
                runOnUiThread { codeRow.visibility = View.GONE }
                uiState(StatusState.PAIRED_CONNECTING, cAccentStroke)
                connectRemote()
                runOnUiThread { show(0) }
            } catch (e: Exception) {
                uiState(StatusState.CODE_REJECTED, cRedStroke, e.message)
            }
        }
    }

    private fun connectClicked() {
        val h = ipBox.text.toString().trim()
        if (h.isEmpty()) {
            uiState(StatusState.ENTER_IP, cRedStroke)
            return
        }
        host = h
        uiState(StatusState.CONNECTING, cAccentStroke)
        fastIo.execute {
            try {
                connectRemote()
                runOnUiThread { show(0) }
            } catch (e: Exception) {
                uiState(StatusState.CONNECT_FAILED, cRedStroke, e.message)
            }
        }
    }

    @Synchronized
    private fun connectRemote() {
        ready = false
        remote?.close()
        val c = openTls(host, 6466, identity(), 0)
        remote = c
        fastIo.execute { readerLoop(c) }
        waitReady()
    }

    private fun waitReady() {
        var waited = 0
        while (!ready && waited < 1200) {
            Thread.sleep(10)
            waited += 10
        }
    }

    private fun configureReply(): ByteArray {
        val info = Pb.str(1, "model") + Pb.str(2, "vendor") + Pb.int(3, 1) +
            Pb.str(4, "1") + Pb.str(5, "androidtv-remote") + Pb.str(6, "1.0.0")
        return Pb.bytes(1, Pb.int(1, 622) + Pb.bytes(2, info))
    }

    private fun readerLoop(c: Conn) {
        try {
            while (true) {
                val m = Pb.parse(c.read())
                for (f in m) {
                    when (f.num) {
                        1 -> c.send(configureReply())
                        2 -> c.send(Pb.bytes(2, Pb.int(1, 622)))
                        8 -> {
                            val v = Pb.parse(f.data).firstOrNull { it.num == 1 }?.number ?: 0L
                            c.send(Pb.bytes(9, Pb.int(1, v.toInt())))
                        }
                        40 -> {
                            ready = true
                            uiState(StatusState.CONNECTED, cGreen)
                        }
                    }
                }
            }
        } catch (_: Exception) {
            if (remote === c) {
                remote = null
                ready = false
                uiState(StatusState.LOST, cRedStroke)
            }
        }
    }

    private fun keyMsg(code: Int) = Pb.bytes(10, Pb.int(1, code) + Pb.int(2, 3))

    private fun writeKey(code: Int) {
        val msg = keyMsg(code)
        val c = remote
        if (c != null) {
            try {
                c.send(msg)
                return
            } catch (_: Exception) {
                remote = null
                ready = false
            }
        }
        if (host.isEmpty()) throw IllegalStateException(strings().statusEnterIpFirst)
        if (!reconnecting) {
            reconnecting = true
            try {
                connectRemote()
            } finally {
                reconnecting = false
            }
        } else {
            waitReady()
        }
        val activeConn = remote ?: throw IllegalStateException(strings().statusConnectFailed)
        activeConn.send(msg)
    }

    private fun sendKey(code: Int) = fastIo.execute {
        try {
            writeKey(code)
        } catch (e: Exception) {
            uiState(StatusState.SEND_FAILED, cRedStroke, e.message)
        }
    }

    override fun onDestroy() {
        super.onDestroy()
        pairConn?.close()
        remote?.close()
        fastIo.shutdownNow()
    }
}
