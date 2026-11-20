package com.example.tvkumanda

import android.annotation.SuppressLint
import android.app.Activity
import android.content.Context
import android.content.res.ColorStateList
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.Paint
import android.graphics.Path
import android.graphics.RectF
import android.graphics.Typeface
import android.graphics.drawable.GradientDrawable
import android.graphics.drawable.RippleDrawable
import android.os.Bundle
import android.util.TypedValue
import android.view.Gravity
import android.view.HapticFeedbackConstants
import android.view.MotionEvent
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
import kotlin.math.atan2
import kotlin.math.cos
import kotlin.math.hypot
import kotlin.math.min
import kotlin.math.sin

object Pb {
    private val EMPTY = ByteArray(0)

    fun writeVarint(out: ByteArrayOutputStream, value: Long) {
        var v = value
        while (true) {
            if ((v and 0x7FL.inv()) == 0L) {
                out.write(v.toInt())
                break
            }
            out.write(((v and 0x7F) or 0x80).toInt())
            v = v ushr 7
        }
    }

    fun varint(value: Long): ByteArray = ByteArrayOutputStream().also { writeVarint(it, value) }.toByteArray()
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
                1 -> { if (i + 8 > b.size) break; i += 8 }
                5 -> { if (i + 4 > b.size) break; i += 4 }
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
    private val frameBuf = ByteArrayOutputStream(256)

    fun send(msg: ByteArray) {
        synchronized(out) {
            frameBuf.reset()
            Pb.writeVarint(frameBuf, msg.size.toLong())
            frameBuf.write(msg)
            frameBuf.writeTo(out)
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

private enum class DpadZone { NONE, UP, RIGHT, DOWN, LEFT, CENTER }

private class DpadWheelView(
    context: Context,
    private val onZoneTap: (DpadZone) -> Unit
) : View(context) {

    private var sliceFill = Color.parseColor("#1D222E")
    private var sliceStroke = Color.parseColor("#2B3242")
    private var pressedSliceFill = Color.parseColor("#2D3648")
    private var centerFill = Color.parseColor("#2563EB")
    private var centerStroke = Color.parseColor("#60A5FA")
    private var centerTextColor = Color.WHITE
    private var arrowColor = Color.parseColor("#F8FAFC")
    private var activeZone = DpadZone.NONE

    private val outerRect = RectF()
    private val innerRect = RectF()
    private val slicePaths = Array(4) { Path() }
    private val fillPaint = Paint(Paint.ANTI_ALIAS_FLAG).apply { style = Paint.Style.FILL }
    private val strokePaint = Paint(Paint.ANTI_ALIAS_FLAG).apply { style = Paint.Style.STROKE }
    private val glyphPaint = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        textAlign = Paint.Align.CENTER
        typeface = Typeface.DEFAULT_BOLD
    }

    fun applyColors(
        sliceFill: Int,
        sliceStroke: Int,
        centerFill: Int,
        centerStroke: Int,
        centerTextColor: Int,
        arrowColor: Int
    ) {
        this.sliceFill = sliceFill
        this.sliceStroke = sliceStroke
        this.pressedSliceFill = lighten(sliceFill, 1.24f)
        this.centerFill = centerFill
        this.centerStroke = centerStroke
        this.centerTextColor = centerTextColor
        this.arrowColor = arrowColor
        invalidate()
    }

    private fun lighten(color: Int, factor: Float): Int = Color.rgb(
        (Color.red(color) * factor).toInt().coerceIn(0, 255),
        (Color.green(color) * factor).toInt().coerceIn(0, 255),
        (Color.blue(color) * factor).toInt().coerceIn(0, 255)
    )

    override fun onMeasure(widthMeasureSpec: Int, heightMeasureSpec: Int) {
        val w = MeasureSpec.getSize(widthMeasureSpec)
        val h = MeasureSpec.getSize(heightMeasureSpec)
        val side = if (h > 0) min(w, h) else w
        val spec = MeasureSpec.makeMeasureSpec(side, MeasureSpec.EXACTLY)
        super.onMeasure(spec, spec)
    }

    override fun onSizeChanged(w: Int, h: Int, oldw: Int, oldh: Int) {
        super.onSizeChanged(w, h, oldw, oldh)
        if (w <= 0 || h <= 0) return
        val cx = w / 2f
        val cy = h / 2f
        val outerR = min(cx, cy) - 4f
        val innerR = outerR * 0.34f
        outerRect.set(cx - outerR, cy - outerR, cx + outerR, cy + outerR)
        innerRect.set(cx - innerR, cy - innerR, cx + innerR, cy + innerR)
        val starts = floatArrayOf(-45f, 45f, 135f, 225f)
        for (i in 0 until 4) {
            slicePaths[i].apply {
                reset()
                arcTo(outerRect, starts[i], 90f, true)
                arcTo(innerRect, starts[i] + 90f, -90f, false)
                close()
            }
        }
    }

    private fun zoneAt(x: Float, y: Float): DpadZone {
        val cx = width / 2f
        val cy = height / 2f
        val outerR = min(cx, cy) - 4f
        val innerR = outerR * 0.34f
        val dx = x - cx
        val dy = y - cy
        val dist = hypot(dx, dy)
        if (dist > outerR) return DpadZone.NONE
        if (dist <= innerR) return DpadZone.CENTER
        var deg = Math.toDegrees(atan2(dy.toDouble(), dx.toDouble())).toFloat()
        if (deg < 0f) deg += 360f
        return when {
            deg >= 315f || deg < 45f -> DpadZone.RIGHT
            deg < 135f -> DpadZone.DOWN
            deg < 225f -> DpadZone.LEFT
            else -> DpadZone.UP
        }
    }

    override fun onDraw(canvas: Canvas) {
        super.onDraw(canvas)
        if (width <= 0 || height <= 0) return
        val cx = width / 2f
        val cy = height / 2f
        val outerR = min(cx, cy) - 4f
        val innerR = outerR * 0.34f
        strokePaint.strokeWidth = maxOf(2f, outerR * 0.015f)
        strokePaint.color = sliceStroke

        val zones = arrayOf(DpadZone.RIGHT, DpadZone.DOWN, DpadZone.LEFT, DpadZone.UP)
        for (i in 0 until 4) {
            fillPaint.color = if (activeZone == zones[i]) pressedSliceFill else sliceFill
            canvas.drawPath(slicePaths[i], fillPaint)
            canvas.drawPath(slicePaths[i], strokePaint)
        }

        val midR = (outerR + innerR) * 0.52f
        glyphPaint.color = arrowColor
        glyphPaint.textSize = outerR * 0.14f
        val offsetY = (glyphPaint.descent() + glyphPaint.ascent()) / 2f
        val glyphs = arrayOf(
            Triple("▲", 270.0, DpadZone.UP),
            Triple("▶", 0.0, DpadZone.RIGHT),
            Triple("▼", 90.0, DpadZone.DOWN),
            Triple("◀", 180.0, DpadZone.LEFT)
        )
        for ((sym, deg, _) in glyphs) {
            val rad = Math.toRadians(deg)
            canvas.drawText(
                sym,
                cx + (midR * cos(rad)).toFloat(),
                cy + (midR * sin(rad)).toFloat() - offsetY,
                glyphPaint
            )
        }

        fillPaint.color = if (activeZone == DpadZone.CENTER) lighten(centerFill, 1.12f) else centerFill
        strokePaint.color = centerStroke
        canvas.drawCircle(cx, cy, innerR, fillPaint)
        canvas.drawCircle(cx, cy, innerR, strokePaint)

        glyphPaint.color = centerTextColor
        glyphPaint.textSize = innerR * 0.52f
        val okOffsetY = (glyphPaint.descent() + glyphPaint.ascent()) / 2f
        canvas.drawText("OK", cx, cy - okOffsetY, glyphPaint)
    }

    @SuppressLint("ClickableViewAccessibility")
    override fun onTouchEvent(event: MotionEvent): Boolean {
        when (event.actionMasked) {
            MotionEvent.ACTION_DOWN, MotionEvent.ACTION_MOVE -> {
                val z = zoneAt(event.x, event.y)
                if (z != activeZone) {
                    activeZone = z
                    invalidate()
                }
                return true
            }
            MotionEvent.ACTION_UP -> {
                val z = zoneAt(event.x, event.y)
                if (z != DpadZone.NONE) onZoneTap(z)
                activeZone = DpadZone.NONE
                invalidate()
                performClick()
                return true
            }
            MotionEvent.ACTION_CANCEL -> {
                activeZone = DpadZone.NONE
                invalidate()
                return true
            }
        }
        return super.onTouchEvent(event)
    }

    override fun performClick(): Boolean = super.performClick()
}

private enum class StatusState {
    DISCONNECTED, ENTER_IP, PAIRING_START, ENTER_CODE, PAIRING_FAILED,
    CODE_LENGTH, CODE_REJECTED, PAIRED_CONNECTING, CONNECTING,
    CONNECT_FAILED, CONNECTED, LOST, PAIR_RESET, SEND_FAILED
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

private val stringsMap = mapOf(
    "tr" to mapOf(
        "tabRemote" to "Kumanda", "tabConnect" to "Bağlantı", "power" to "Güç",
        "tvIp" to "TV IP Adresi", "settings" to "Ayarlar", "theme" to "Renk Paleti",
        "lang" to "Dil", "codeHint" to "6 haneli kod", "confirm" to "Onayla",
        "connect" to "Bağlan", "hapticOn" to "Titreşim: Açık", "hapticOff" to "Titreşim: Kapalı",
        "autoOn" to "Oto Bağlan: Açık", "autoOff" to "Oto Bağlan: Kapalı",
        "resetPair" to "Eşleştirmeyi Sıfırla",
        StatusState.DISCONNECTED.name to "Bağlı değil",
        StatusState.ENTER_IP.name to "Önce TV'nin IP adresini yaz",
        StatusState.PAIRING_START.name to "Eşleştirme başlıyor…",
        StatusState.ENTER_CODE.name to "TV'deki 6 haneli kodu yazıp Onayla'ya bas",
        StatusState.PAIRING_FAILED.name to "Eşleştirme başarısız",
        StatusState.CODE_LENGTH.name to "Kod 6 karakter olmalı",
        StatusState.CODE_REJECTED.name to "Kod kabul edilmedi",
        StatusState.PAIRED_CONNECTING.name to "Eşleşti — Bağlanıyor…",
        StatusState.CONNECTING.name to "Bağlanıyor…",
        StatusState.CONNECT_FAILED.name to "Bağlanamadı",
        StatusState.CONNECTED.name to "Bağlandı",
        StatusState.LOST.name to "Bağlantı koptu",
        StatusState.PAIR_RESET.name to "Eşleştirme sıfırlandı",
        StatusState.SEND_FAILED.name to "Gönderilemedi"
    ),
    "en" to mapOf(
        "tabRemote" to "Remote", "tabConnect" to "Connection", "power" to "Power",
        "tvIp" to "TV IP Address", "settings" to "Settings", "theme" to "Color Palette",
        "lang" to "Language", "codeHint" to "6-digit code", "confirm" to "Confirm",
        "connect" to "Connect", "hapticOn" to "Haptic: On", "hapticOff" to "Haptic: Off",
        "autoOn" to "Auto Connect: On", "autoOff" to "Auto Connect: Off",
        "resetPair" to "Reset Pairing",
        StatusState.DISCONNECTED.name to "Disconnected",
        StatusState.ENTER_IP.name to "Enter the TV IP address first",
        StatusState.PAIRING_START.name to "Starting pairing…",
        StatusState.ENTER_CODE.name to "Enter the 6-digit code on TV and tap Confirm",
        StatusState.PAIRING_FAILED.name to "Pairing failed",
        StatusState.CODE_LENGTH.name to "Code must be 6 characters",
        StatusState.CODE_REJECTED.name to "Code rejected",
        StatusState.PAIRED_CONNECTING.name to "Paired — Connecting…",
        StatusState.CONNECTING.name to "Connecting…",
        StatusState.CONNECT_FAILED.name to "Connection failed",
        StatusState.CONNECTED.name to "Connected",
        StatusState.LOST.name to "Connection lost",
        StatusState.PAIR_RESET.name to "Pairing reset",
        StatusState.SEND_FAILED.name to "Failed to send"
    ),
    "ru" to mapOf(
        "tabRemote" to "Пульт", "tabConnect" to "Подключение", "power" to "Питание",
        "tvIp" to "IP-адрес ТВ", "settings" to "Настройки", "theme" to "Палитра цветов",
        "lang" to "Язык", "codeHint" to "6-значный код", "confirm" to "ОК",
        "connect" to "Подключить", "hapticOn" to "Вибрация: Вкл", "hapticOff" to "Вибрация: Выкл",
        "autoOn" to "Автоподкл.: Вкл", "autoOff" to "Автоподкл.: Выкл",
        "resetPair" to "Сбросить пару",
        StatusState.DISCONNECTED.name to "Не подключено",
        StatusState.ENTER_IP.name to "Сначала введите IP-адрес ТВ",
        StatusState.PAIRING_START.name to "Начинаем сопряжение…",
        StatusState.ENTER_CODE.name to "Введите 6-значный код с ТВ и нажмите ОК",
        StatusState.PAIRING_FAILED.name to "Ошибка сопряжения",
        StatusState.CODE_LENGTH.name to "Код должен быть из 6 символов",
        StatusState.CODE_REJECTED.name to "Код отклонён",
        StatusState.PAIRED_CONNECTING.name to "Сопряжено — Подключение…",
        StatusState.CONNECTING.name to "Подключение…",
        StatusState.CONNECT_FAILED.name to "Не удалось подключиться",
        StatusState.CONNECTED.name to "Подключено",
        StatusState.LOST.name to "Соединение потеряно",
        StatusState.PAIR_RESET.name to "Сопряжение сброшено",
        StatusState.SEND_FAILED.name to "Ошибка отправки"
    ),
    "az" to mapOf(
        "tabRemote" to "Pult", "tabConnect" to "Bağlantı", "power" to "Güc",
        "tvIp" to "TV IP Ünvanı", "settings" to "Ayarlar", "theme" to "Rəng Palitrası",
        "lang" to "Dil", "codeHint" to "6 rəqəmli kod", "confirm" to "Təsdiqlə",
        "connect" to "Qoşul", "hapticOn" to "Titrəmə: Açıq", "hapticOff" to "Titrəmə: Bağlı",
        "autoOn" to "Avto Qoşul: Açıq", "autoOff" to "Avto Qoşul: Bağlı",
        "resetPair" to "Cütləşməni Sıfırla",
        StatusState.DISCONNECTED.name to "Qoşulu deyil",
        StatusState.ENTER_IP.name to "Əvvəlcə TV-nin IP ünvanını yaz",
        StatusState.PAIRING_START.name to "Cütləşmə başlayır…",
        StatusState.ENTER_CODE.name to "TV-dəki 6 rəqəmli kodu yazıb Təsdiqlə bas",
        StatusState.PAIRING_FAILED.name to "Cütləşmə uğursuz oldu",
        StatusState.CODE_LENGTH.name to "Kod 6 simvol olmalıdır",
        StatusState.CODE_REJECTED.name to "Kod qəbul edilmədi",
        StatusState.PAIRED_CONNECTING.name to "Cütləşdi — Qoşulur…",
        StatusState.CONNECTING.name to "Qoşulur…",
        StatusState.CONNECT_FAILED.name to "Qoşulmaq olmadı",
        StatusState.CONNECTED.name to "Qoşuldu",
        StatusState.LOST.name to "Bağlantı kəsildi",
        StatusState.PAIR_RESET.name to "Cütləşmə sıfırlandı",
        StatusState.SEND_FAILED.name to "Göndərilə bilmədi"
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
    private var settingsOpen = false
    private var lastStatusState = StatusState.DISCONNECTED
    private var lastStatusDetail: String? = null
    private var lastStatusDotColor = Color.parseColor("#64748B")

    private val palettes = listOf(
        ColorPalette("Mavi", Color.parseColor("#0B0D12"), Color.parseColor("#141821"), Color.parseColor("#10141C"), Color.parseColor("#1D222E"), Color.parseColor("#2B3242"), Color.parseColor("#2563EB"), Color.parseColor("#60A5FA")),
        ColorPalette("Zümrüt", Color.parseColor("#09110E"), Color.parseColor("#111F1A"), Color.parseColor("#0D1814"), Color.parseColor("#182B24"), Color.parseColor("#264237"), Color.parseColor("#059669"), Color.parseColor("#34D399")),
        ColorPalette("Mor", Color.parseColor("#0E0B14"), Color.parseColor("#191424"), Color.parseColor("#13101C"), Color.parseColor("#241D33"), Color.parseColor("#362C4D"), Color.parseColor("#7C3AED"), Color.parseColor("#A78BFA")),
        ColorPalette("Kehribar", Color.parseColor("#120E09"), Color.parseColor("#201810"), Color.parseColor("#18120C"), Color.parseColor("#2E2216"), Color.parseColor("#453321"), Color.parseColor("#D97706"), Color.parseColor("#FBBF24")),
        ColorPalette("Siyah Beyaz", Color.parseColor("#000000"), Color.parseColor("#121212"), Color.parseColor("#0A0A0A"), Color.parseColor("#1E1E1E"), Color.parseColor("#4A4A4A"), Color.parseColor("#FFFFFF"), Color.parseColor("#FFFFFF"), Color.parseColor("#000000"))
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
    private lateinit var dpadWheelView: DpadWheelView
    private lateinit var powerBtnView: Button
    private lateinit var connectCardView: LinearLayout
    private lateinit var settingsScrollView: ScrollView
    private lateinit var settingsCardView: LinearLayout
    private lateinit var tvIpTitleView: TextView
    private lateinit var settingsTitleView: TextView
    private lateinit var themeSectionView: TextView
    private lateinit var langSectionView: TextView
    private lateinit var openSettingsBtnView: Button
    private lateinit var connectBtnView: Button
    private lateinit var resetPairBtnView: Button
    private lateinit var confirmPairBtnView: Button
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
    private val paletteRows = ArrayList<Pair<Int, LinearLayout>>()
    private val langRows = ArrayList<Pair<String, LinearLayout>>()
    private val screens = ArrayList<View>()

    private fun t(key: String): String =
        stringsMap[currentLang]?.get(key) ?: stringsMap.getValue("tr").getValue(key)

    private fun px(v: Int) = (v * dp).toInt()
    private fun scaledSp(v: Float) = v * (sp / dp).coerceIn(0.85f, 1.3f)
    private fun lp(w: Int, h: Int, weight: Float = 0f, l: Int = 0, top: Int = 0, r: Int = 0, b: Int = 0) =
        LinearLayout.LayoutParams(w, h, weight).apply { setMargins(px(l), px(top), px(r), px(b)) }

    private fun tap(type: Int = HapticFeedbackConstants.VIRTUAL_KEY, v: View? = null) {
        if (hapticEnabled) v?.performHapticFeedback(type) ?: window.decorView.performHapticFeedback(type)
    }

    private fun makePillBg(fill: Int, stroke: Int, radiusDp: Int = 22): RippleDrawable {
        val shape = GradientDrawable().apply {
            shape = GradientDrawable.RECTANGLE
            cornerRadius = px(radiusDp).toFloat()
            setColor(fill)
            setStroke(px(2), stroke)
        }
        return RippleDrawable(ColorStateList.valueOf(Color.parseColor("#38FFFFFF")), shape, null)
    }

    private fun makeCardBg(fill: Int = cSurface, stroke: Int = cBtnStroke, radiusDp: Int = 26): GradientDrawable =
        GradientDrawable().apply {
            shape = GradientDrawable.RECTANGLE
            cornerRadius = px(radiusDp).toFloat()
            setColor(fill)
            setStroke(px(1), stroke)
        }

    private fun makeInputBg(): GradientDrawable = makeCardBg(cCard, cBtnStroke, 18)

    private fun styleBtn(b: Button, fill: Int, stroke: Int, textColor: Int, sizeSp: Float, radiusDp: Int = 22) {
        b.background = makePillBg(fill, stroke, radiusDp)
        b.setTextColor(textColor)
        b.typeface = Typeface.DEFAULT_BOLD
        b.isAllCaps = false
        b.setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(sizeSp))
        b.setPadding(px(6), 0, px(6), 0)
        b.minWidth = 0; b.minimumWidth = 0; b.minHeight = 0; b.minimumHeight = 0
    }

    private fun sectionLabel(key: String, topMargin: Int = 12) = TextView(this).apply {
        text = t(key)
        setTextColor(cSubtext)
        typeface = Typeface.DEFAULT_BOLD
        setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(13.5f))
        setPadding(px(2), px(topMargin), 0, px(6))
    }

    private fun optionRow(title: String, dotColor: Int?, onClick: () -> Unit) = LinearLayout(this).apply {
        orientation = LinearLayout.HORIZONTAL
        gravity = Gravity.CENTER_VERTICAL
        isClickable = true; isFocusable = true
        setPadding(px(14), px(12), px(14), px(12))
        layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT, 0f, 0, 0, 0, 6)
        if (dotColor != null) {
            addView(View(this@MainActivity).apply {
                layoutParams = lp(px(12), px(12), 0f, 0, 0, 10, 0)
                background = GradientDrawable().apply { shape = GradientDrawable.OVAL; setColor(dotColor) }
            })
        }
        addView(TextView(this@MainActivity).apply {
            text = title
            typeface = Typeface.DEFAULT_BOLD
            setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(14f))
            layoutParams = lp(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f)
        })
        addView(TextView(this@MainActivity).apply {
            typeface = Typeface.DEFAULT_BOLD
            setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(13f))
        })
        setOnClickListener { tap(HapticFeedbackConstants.KEYBOARD_TAP, this); onClick() }
    }

    private fun formatStatus(state: StatusState, detail: String?): String {
        val base = t(state.name)
        return if (!detail.isNullOrBlank()) "$base: $detail" else base
    }

    private fun show(i: Int) {
        currentScreen = i
        screens.forEachIndexed { n, sc -> sc.visibility = if (n == i) View.VISIBLE else View.GONE }
        if (i != 1 && settingsOpen) {
            settingsOpen = false
            settingsScrollView.visibility = View.GONE
        }
        navBtns.forEachIndexed { n, b ->
            val active = n == i
            b.background = makePillBg(if (active) cAccent else cCard, if (active) cAccentStroke else cBtnStroke)
            b.setTextColor(if (active) cAccentText else cSubtext)
        }
    }

    private fun refreshOptionRows() {
        paletteRows.forEach { (idx, rowView) ->
            val selected = idx == paletteIndex
            val p = palettes[idx]
            rowView.background = makeCardBg(if (selected) cCard else cBtn, if (selected) p.accentStroke else cBtnStroke, 16)
            val tv = rowView.getChildAt(1) as? TextView
            tv?.text = p.name
            tv?.setTextColor(if (selected) cText else cSubtext)
            val mark = rowView.getChildAt(2) as? TextView
            mark?.text = if (selected) "●" else ""
            mark?.setTextColor(p.accentStroke)
        }
        langRows.forEach { (code, rowView) ->
            val selected = code == currentLang
            rowView.background = makeCardBg(if (selected) cCard else cBtn, if (selected) cAccentStroke else cBtnStroke, 16)
            val tv = rowView.getChildAt(0) as? TextView
            tv?.setTextColor(if (selected) cText else cSubtext)
            val mark = rowView.getChildAt(1) as? TextView
            mark?.text = if (selected) "●" else ""
            mark?.setTextColor(cAccentStroke)
        }
    }

    private fun applyLanguage(lang: String) {
        currentLang = if (stringsMap.containsKey(lang)) lang else "tr"
        if (navBtns.size >= 2) {
            navBtns[0].text = t("tabRemote")
            navBtns[1].text = t("tabConnect")
        }
        powerBtnView.text = t("power")
        tvIpTitleView.text = t("tvIp")
        openSettingsBtnView.text = t("settings")
        settingsTitleView.text = t("settings")
        themeSectionView.text = t("theme")
        langSectionView.text = t("lang")
        codeBox.hint = t("codeHint")
        confirmPairBtnView.text = t("confirm")
        connectBtnView.text = t("connect")
        hapticBtn.text = t(if (hapticEnabled) "hapticOn" else "hapticOff")
        autoConnectBtn.text = t(if (autoConnectEnabled) "autoOn" else "autoOff")
        resetPairBtnView.text = t("resetPair")
        status.text = formatStatus(lastStatusState, lastStatusDetail)
        (statusDot.background as? GradientDrawable)?.setColor(lastStatusDotColor)
        refreshOptionRows()
    }

    private fun applyPalette(index: Int) {
        val p = palettes[index.coerceIn(0, palettes.lastIndex)]
        paletteIndex = index
        cBg = p.bg; cCard = p.card; cSurface = p.surface
        cBtn = p.btn; cBtnStroke = p.btnStroke
        cAccent = p.accent; cAccentStroke = p.accentStroke; cAccentText = p.accentText

        rootView.setBackgroundColor(cBg)
        topBarView.background = makeCardBg(cCard, cBtnStroke, 20)
        connectCardView.background = makeCardBg(cSurface, cBtnStroke, 28)
        settingsCardView.background = makeCardBg(cSurface, cBtnStroke, 28)
        dpadWheelView.applyColors(cBtn, cBtnStroke, cAccent, cAccentStroke, cAccentText, cText)
        ipBox.background = makeInputBg()
        codeBox.background = makeInputBg()

        neutralPillBtns.forEach { styleBtn(it, cBtn, cBtnStroke, cText, if (it.text.length <= 2) 19f else 17.5f) }
        styleBtn(powerBtnView, cRedSoft, cRedStroke, cText, 15.5f)
        styleBtn(openSettingsBtnView, if (settingsOpen) cAccent else cBtn, if (settingsOpen) cAccentStroke else cBtnStroke, if (settingsOpen) cAccentText else cText, 15.5f, 18)
        styleBtn(connectBtnView, cAccent, cAccentStroke, cAccentText, 16f, 18)
        styleBtn(confirmPairBtnView, cAccent, cAccentStroke, cAccentText, 15f, 18)
        styleBtn(resetPairBtnView, cRedSoft, cRedStroke, cText, 14f, 16)
        styleBtn(hapticBtn, if (hapticEnabled) cBtn else cCard, cBtnStroke, if (hapticEnabled) cText else cSubtext, 14f, 16)
        styleBtn(autoConnectBtn, if (autoConnectEnabled) cBtn else cCard, cBtnStroke, if (autoConnectEnabled) cText else cSubtext, 14f, 16)

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

        ipBox = EditText(this).apply {
            hint = "192.168.1.105"
            setHintTextColor(cMuted); setTextColor(cText)
            typeface = Typeface.DEFAULT_BOLD
            setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(17f))
            setPadding(px(18), px(15), px(18), px(15))
            setText(prefs.getString("ip", ""))
            setSingleLine()
            layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT, 0f, 0, 0, 0, 12)
        }
        codeBox = EditText(this).apply {
            hint = t("codeHint")
            setHintTextColor(cMuted); setTextColor(cText)
            typeface = Typeface.DEFAULT_BOLD
            setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(16f))
            setPadding(px(16), px(14), px(16), px(14))
            setSingleLine()
            layoutParams = lp(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f, 0, 0, 10, 0)
        }
        confirmPairBtnView = Button(this).apply {
            text = t("confirm")
            layoutParams = lp(LinearLayout.LayoutParams.WRAP_CONTENT, px(52))
            setOnClickListener { tap(HapticFeedbackConstants.KEYBOARD_TAP, this); finishPairing(codeBox.text.toString()) }
        }
        codeRow = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL
            visibility = View.GONE; setPadding(0, px(12), 0, 0)
            addView(codeBox); addView(confirmPairBtnView)
        }
        statusDot = View(this).apply {
            layoutParams = lp(px(10), px(10), 0f, 0, 0, 10, 0)
            background = GradientDrawable().apply { shape = GradientDrawable.OVAL; setColor(cMuted) }
        }
        status = TextView(this).apply {
            text = formatStatus(lastStatusState, null)
            setTextColor(cSubtext)
            setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(13.5f))
            setSingleLine()
        }
        powerBtnView = Button(this).apply {
            text = t("power")
            layoutParams = lp(px(110), LinearLayout.LayoutParams.MATCH_PARENT)
            setOnClickListener { tap(HapticFeedbackConstants.VIRTUAL_KEY, this); sendKey(26) }
        }
        dpadWheelView = DpadWheelView(this) { zone ->
            tap(HapticFeedbackConstants.VIRTUAL_KEY, dpadWheelView)
            when (zone) {
                DpadZone.UP -> sendKey(19)
                DpadZone.RIGHT -> sendKey(22)
                DpadZone.DOWN -> sendKey(20)
                DpadZone.LEFT -> sendKey(21)
                DpadZone.CENTER -> sendKey(23)
                DpadZone.NONE -> Unit
            }
        }.apply { layoutParams = lp(px(250), px(250), 0f, 0, 8, 0, 8) }

        val remoteScreenView = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL; gravity = Gravity.CENTER_HORIZONTAL
            visibility = View.GONE; setPadding(px(14), px(6), px(14), px(8))
            addView(row(View(this@MainActivity).apply { layoutParams = lp(0, px(1), 1f) }, powerBtnView).apply {
                layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, px(52), 0f, 0, 2, 0, 10)
            })
            addView(row(pillKey("🔊+", 24, 1.15f), pillKey("🔇", 164, 0.9f), pillKey("🔊−", 25, 1.15f)).apply {
                layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, px(54), 0f, 0, 0, 0, 10)
            })
            addView(LinearLayout(this@MainActivity).apply {
                orientation = LinearLayout.VERTICAL; gravity = Gravity.CENTER
                layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, 0, 1f)
                addView(dpadWheelView)
            })
            addView(row(pillKey("↩", 4), pillKey("⌂", 3), pillKey("⚙", 176)).apply {
                layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, px(54), 0f, 0, 8, 0, 2)
            })
        }
        screens.add(remoteScreenView)

        connectBtnView = Button(this).apply {
            text = t("connect")
            layoutParams = lp(0, px(54), 1f, 0, 0, 6, 0)
            setOnClickListener {
                tap(HapticFeedbackConstants.KEYBOARD_TAP, this)
                prefs.edit().putString("ip", ipBox.text.toString().trim()).apply()
                if (prefs.getBoolean("paired", false)) connectClicked() else startPairing()
            }
        }
        openSettingsBtnView = Button(this).apply {
            text = t("settings")
            layoutParams = lp(0, px(54), 1f, 6, 0, 0, 0)
            setOnClickListener {
                tap(HapticFeedbackConstants.KEYBOARD_TAP, this)
                settingsOpen = !settingsOpen
                settingsScrollView.visibility = if (settingsOpen) View.VISIBLE else View.GONE
                styleBtn(this, if (settingsOpen) cAccent else cBtn, if (settingsOpen) cAccentStroke else cBtnStroke, if (settingsOpen) cAccentText else cText, 15.5f, 18)
            }
        }
        tvIpTitleView = TextView(this).apply {
            text = t("tvIp"); setTextColor(cText); typeface = Typeface.DEFAULT_BOLD
            setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(18f)); setPadding(px(2), 0, 0, px(10))
        }
        connectCardView = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL; setPadding(px(16), px(18), px(16), px(18))
            layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT)
            addView(tvIpTitleView); addView(ipBox)
            addView(row(connectBtnView, openSettingsBtnView).apply {
                layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT)
            })
            addView(codeRow)
        }

        hapticBtn = Button(this).apply {
            text = t(if (hapticEnabled) "hapticOn" else "hapticOff")
            layoutParams = lp(0, px(48), 1f, 0, 0, 6, 0)
            setOnClickListener {
                hapticEnabled = !hapticEnabled
                prefs.edit().putBoolean("haptic", hapticEnabled).apply()
                text = t(if (hapticEnabled) "hapticOn" else "hapticOff")
                styleBtn(this, if (hapticEnabled) cBtn else cCard, cBtnStroke, if (hapticEnabled) cText else cSubtext, 14f, 16)
                tap(HapticFeedbackConstants.KEYBOARD_TAP, this)
            }
        }
        autoConnectBtn = Button(this).apply {
            text = t(if (autoConnectEnabled) "autoOn" else "autoOff")
            layoutParams = lp(0, px(48), 1f, 6, 0, 0, 0)
            setOnClickListener {
                tap(HapticFeedbackConstants.KEYBOARD_TAP, this)
                autoConnectEnabled = !autoConnectEnabled
                prefs.edit().putBoolean("auto_connect", autoConnectEnabled).apply()
                text = t(if (autoConnectEnabled) "autoOn" else "autoOff")
                styleBtn(this, if (autoConnectEnabled) cBtn else cCard, cBtnStroke, if (autoConnectEnabled) cText else cSubtext, 14f, 16)
            }
        }
        resetPairBtnView = Button(this).apply {
            text = t("resetPair")
            layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, px(48), 0f, 0, 14, 0, 0)
            setOnClickListener {
                tap(HapticFeedbackConstants.KEYBOARD_TAP, this)
                prefs.edit().putBoolean("paired", false).apply()
                pairConn?.close(); pairConn = null
                remote?.close(); remote = null
                ready = false; codeRow.visibility = View.GONE
                uiState(StatusState.PAIR_RESET, cMuted)
            }
        }
        settingsTitleView = TextView(this).apply {
            text = t("settings"); setTextColor(cText); typeface = Typeface.DEFAULT_BOLD
            setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(17.5f)); setPadding(px(2), 0, 0, px(10))
        }
        themeSectionView = sectionLabel("theme")
        langSectionView = sectionLabel("lang")

        settingsCardView = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL; setPadding(px(16), px(16), px(16), px(16))
            addView(settingsTitleView)
            addView(row(hapticBtn, autoConnectBtn).apply {
                layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT)
            })
            addView(themeSectionView)
            palettes.forEachIndexed { idx, p ->
                val r = optionRow(p.name, p.accent) {
                    prefs.edit().putInt("palette", idx).apply()
                    applyPalette(idx)
                }
                paletteRows.add(idx to r); addView(r)
            }
            addView(langSectionView)
            listOf("tr" to "Türkçe", "en" to "English", "ru" to "Русский", "az" to "Azərbaycan").forEach { (code, label) ->
                val r = optionRow(label, null) {
                    prefs.edit().putString("lang", code).apply()
                    applyLanguage(code)
                }
                langRows.add(code to r); addView(r)
            }
            addView(resetPairBtnView)
        }

        settingsScrollView = ScrollView(this).apply {
            visibility = View.GONE; overScrollMode = View.OVER_SCROLL_NEVER
            layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT, 0f, 0, 12, 0, 0)
            addView(settingsCardView)
        }

        screens.add(ScrollView(this).apply {
            visibility = View.GONE; isFillViewport = true; overScrollMode = View.OVER_SCROLL_NEVER
            setPadding(px(14), px(10), px(14), px(12))
            addView(LinearLayout(this@MainActivity).apply {
                orientation = LinearLayout.VERTICAL; gravity = Gravity.CENTER_HORIZONTAL
                layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT)
                addView(connectCardView); addView(settingsScrollView)
            })
        })

        topBarView = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL
            setPadding(px(16), px(11), px(16), px(11))
            layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT, 0f, 14, 2, 14, 6)
            addView(statusDot); addView(status)
        }

        val content = FrameLayout(this).apply {
            layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, 0, 1f)
            screens.forEach { addView(it, FrameLayout.LayoutParams(FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.MATCH_PARENT)) }
        }

        val bottomNav = row(nav(t("tabRemote"), 0), nav(t("tabConnect"), 1)).apply {
            setPadding(px(8), px(2), px(8), px(4))
        }

        rootView = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL; setPadding(px(4), px(26), px(4), px(6))
            addView(topBarView); addView(content); addView(bottomNav)
        }
        setContentView(rootView)

        applyPalette(paletteIndex)
        if (paired && ipBox.text.isNotBlank()) {
            show(0)
            if (autoConnectEnabled) connectClicked()
        } else {
            show(1)
        }
    }

    private fun nav(label: String, i: Int) = Button(this).apply {
        text = label
        typeface = Typeface.DEFAULT_BOLD; isAllCaps = false
        setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(14f))
        setPadding(px(6), px(2), px(6), px(2))
        layoutParams = lp(0, px(54), 1f, 5, 2, 5, 4)
        navBtns.add(this)
        setOnClickListener { tap(HapticFeedbackConstants.KEYBOARD_TAP, this); show(i) }
    }

    private fun row(vararg views: View) = LinearLayout(this).apply {
        orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER
        views.forEach { addView(it) }
    }

    private fun pillKey(label: String, code: Int, weight: Float = 1f) = Button(this).apply {
        text = label
        layoutParams = lp(0, LinearLayout.LayoutParams.MATCH_PARENT, weight, 5, 0, 5, 0)
        neutralPillBtns.add(this)
        setOnClickListener { tap(HapticFeedbackConstants.VIRTUAL_KEY, this); sendKey(code) }
    }

    private fun uiState(state: StatusState, dotColor: Int, detail: String? = null) = runOnUiThread {
        lastStatusState = state; lastStatusDetail = detail; lastStatusDotColor = dotColor
        status.text = formatStatus(state, detail)
        (statusDot.background as? GradientDrawable)?.setColor(dotColor)
    }

    private fun identity(): Identity {
        identity?.let { return it }
        val kf = File(filesDir, "client.key")
        val cf = File(filesDir, "client.crt")
        val id = if (kf.exists() && cf.exists()) {
            Identity(
                KeyFactory.getInstance("RSA").generatePrivate(PKCS8EncodedKeySpec(kf.readBytes())),
                CertificateFactory.getInstance("X.509").generateCertificate(cf.inputStream()) as X509Certificate
            )
        } else {
            val kp = KeyPairGenerator.getInstance("RSA").apply { initialize(2048) }.generateKeyPair()
            val name = X500Name("CN=atvremote")
            val now = Date()
            val cert = JcaX509CertificateConverter().getCertificate(
                JcaX509v3CertificateBuilder(name, BigInteger.valueOf(System.currentTimeMillis()), now, Date(now.time + 20L * 365L * 24L * 3600L * 1000L), name, kp.public)
                    .build(JcaContentSignerBuilder("SHA256withRSA").build(kp.private))
            )
            kf.writeBytes(kp.private.encoded); cf.writeBytes(cert.encoded)
            Identity(kp.private, cert)
        }
        identity = id
        return id
    }

    private fun openTls(h: String, port: Int, id: Identity, readTimeoutMs: Int): Conn {
        val ctx = SSLContext.getInstance("TLS").apply {
            init(arrayOf<KeyManager>(FixedKm(id)), arrayOf<TrustManager>(TrustAll()), null)
        }
        val s = (ctx.socketFactory.createSocket() as SSLSocket).apply {
            connect(InetSocketAddress(h, port), 2000)
            tcpNoDelay = true
            soTimeout = readTimeoutMs
            startHandshake()
        }
        return Conn(s)
    }

    private fun outer(field: Int, inner: ByteArray) = Pb.int(1, 2) + Pb.int(2, 200) + Pb.bytes(field, inner)

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
        if (h.isEmpty()) { uiState(StatusState.ENTER_IP, cRedStroke); return }
        host = h
        uiState(StatusState.PAIRING_START, cAccentStroke)
        fastIo.execute {
            try {
                pairConn?.close()
                val c = openTls(h, 6467, identity(), 10000)
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
        if (code.length != 6) { uiState(StatusState.CODE_LENGTH, cRedStroke); return }
        fastIo.execute {
            try {
                val c = pairConn ?: throw IllegalStateException(t("connect"))
                val serverCert = pairServerCert ?: throw IllegalStateException("Cert")
                val id = identity()
                val clientPub = id.cert.publicKey as RSAPublicKey
                val serverPub = serverCert.publicKey as RSAPublicKey
                val secret = MessageDigest.getInstance("SHA-256").apply {
                    update(clientPub.modulus.unsigned()); update(clientPub.publicExponent.unsigned())
                    update(serverPub.modulus.unsigned()); update(serverPub.publicExponent.unsigned())
                    update(hexToBytes(code.substring(2)))
                }.digest()
                c.send(outer(40, Pb.bytes(1, secret)))
                expect(c, 41)
                c.close(); pairConn = null
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
        if (h.isEmpty()) { uiState(StatusState.ENTER_IP, cRedStroke); return }
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
        while (!ready && waited < 1200) { Thread.sleep(10); waited += 10 }
    }

    private fun configureReply(): ByteArray {
        val info = Pb.str(1, "model") + Pb.str(2, "vendor") + Pb.int(3, 1) +
            Pb.str(4, "1") + Pb.str(5, "androidtv-remote") + Pb.str(6, "1.0.0")
        return Pb.bytes(1, Pb.int(1, 622) + Pb.bytes(2, info))
    }

    private fun readerLoop(c: Conn) {
        try {
            while (true) {
                for (f in Pb.parse(c.read())) {
                    when (f.num) {
                        1 -> c.send(configureReply())
                        2 -> c.send(Pb.bytes(2, Pb.int(1, 622)))
                        8 -> {
                            val v = Pb.parse(f.data).firstOrNull { it.num == 1 }?.number ?: 0L
                            c.send(Pb.bytes(9, Pb.int(1, v.toInt())))
                        }
                        40 -> { ready = true; uiState(StatusState.CONNECTED, cGreen) }
                    }
                }
            }
        } catch (_: Exception) {
            if (remote === c) { remote = null; ready = false; uiState(StatusState.LOST, cRedStroke) }
        }
    }

    private fun writeKey(code: Int) {
        val msg = Pb.bytes(10, Pb.int(1, code) + Pb.int(2, 3))
        val c = remote
        if (c != null) {
            try { c.send(msg); return } catch (_: Exception) { remote = null; ready = false }
        }
        if (host.isEmpty()) throw IllegalStateException(t(StatusState.ENTER_IP.name))
        if (!reconnecting) {
            reconnecting = true
            try { connectRemote() } finally { reconnecting = false }
        } else {
            waitReady()
        }
        (remote ?: throw IllegalStateException(t(StatusState.CONNECT_FAILED.name))).send(msg)
    }

    private fun sendKey(code: Int) = fastIo.execute {
        try { writeKey(code) } catch (e: Exception) { uiState(StatusState.SEND_FAILED, cRedStroke, e.message) }
    }

    override fun onDestroy() {
        super.onDestroy()
        pairConn?.close()
        remote?.close()
        fastIo.shutdownNow()
    }
}
