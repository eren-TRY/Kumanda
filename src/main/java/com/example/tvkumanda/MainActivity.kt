package com.example.tvkumanda

import android.animation.ObjectAnimator
import android.annotation.SuppressLint
import android.app.Activity
import android.content.Context
import android.content.Intent
import android.content.res.ColorStateList
import android.graphics.*
import android.graphics.drawable.GradientDrawable
import android.graphics.drawable.RippleDrawable
import android.net.ConnectivityManager
import android.net.Uri
import android.os.*
import android.util.TypedValue
import android.view.*
import android.widget.*
import org.bouncycastle.asn1.x500.X500Name
import org.bouncycastle.cert.jcajce.JcaX509CertificateConverter
import org.bouncycastle.cert.jcajce.JcaX509v3CertificateBuilder
import org.bouncycastle.operator.jcajce.JcaContentSignerBuilder
import java.io.ByteArrayOutputStream
import java.io.EOFException
import java.io.File
import java.math.BigInteger
import java.net.Inet4Address
import java.net.InetSocketAddress
import java.net.Socket
import java.security.*
import java.security.cert.CertificateFactory
import java.security.cert.X509Certificate
import java.security.interfaces.RSAPublicKey
import java.security.spec.PKCS8EncodedKeySpec
import java.util.*
import java.util.concurrent.CountDownLatch
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit
import javax.net.ssl.*
import kotlin.math.*

object Pb {
    private val EMPTY = ByteArray(0)
    fun writeVarint(out: ByteArrayOutputStream, value: Long) {
        var v = value
        while (true) {
            if ((v and 0x7FL.inv()) == 0L) { out.write(v.toInt()); break }
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
            var r = 0L; var shift = 0
            while (i < b.size) {
                val x = b[i++].toInt() and 0xFF
                r = r or ((x and 0x7F).toLong() shl shift)
                if ((x and 0x80) == 0 || ++shift > 63) return r
            }
            return r
        }
        while (i < b.size) {
            val key = readVar().toInt(); val num = key ushr 3
            if (num <= 0) break
            when (key and 7) {
                0 -> out.add(Field(num, readVar(), EMPTY))
                2 -> {
                    val len = readVar().toInt()
                    if (len < 0 || i + len > b.size) break
                    out.add(Field(num, 0, b.copyOfRange(i, i + len))); i += len
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
    fun send(msg: ByteArray) = synchronized(out) {
        frameBuf.reset(); Pb.writeVarint(frameBuf, msg.size.toLong()); frameBuf.write(msg)
        frameBuf.writeTo(out); out.flush()
    }
    fun read(): ByteArray {
        var len = 0; var shift = 0
        while (true) {
            val b = inp.read(); if (b < 0) throw EOFException("Bağlantı kapandı")
            len = len or ((b and 0x7F) shl shift)
            if ((b and 0x80) == 0) break; shift += 7
        }
        if (len < 0 || len > 1024 * 1024) throw IllegalStateException("Geçersiz paket boyutu: $len")
        val buf = ByteArray(len); var off = 0
        while (off < len) { val n = inp.read(buf, off, len - off); if (n < 0) throw EOFException("Bağlantı kapandı"); off += n }
        return buf
    }
    fun close() { try { sock.close() } catch (_: Exception) {} }
}

private class FixedKm(val id: Identity) : X509KeyManager {
    override fun getClientAliases(k: String?, i: Array<Principal>?) = arrayOf("c")
    override fun chooseClientAlias(k: Array<String>?, i: Array<Principal>?, s: Socket?) = "c"
    override fun getServerAliases(k: String?, i: Array<Principal>?): Array<String>? = null
    override fun chooseServerAlias(k: String?, i: Array<Principal>?, s: Socket?): String? = null
    override fun getCertificateChain(a: String?) = arrayOf(id.cert)
    override fun getPrivateKey(a: String?) = id.key
}

private class TrustAll : X509TrustManager {
    override fun checkClientTrusted(c: Array<out X509Certificate>?, a: String?) {}
    override fun checkServerTrusted(c: Array<out X509Certificate>?, a: String?) {}
    override fun getAcceptedIssuers(): Array<X509Certificate> = arrayOf()
}

private fun BigInteger.unsigned(): ByteArray = toByteArray().let { if (it.size > 1 && it[0] == 0.toByte()) it.copyOfRange(1, it.size) else it }
private fun hexToBytes(s: String): ByteArray {
    require(s.length % 2 == 0) { "Hex uzunluğu çift olmalı" }
    return ByteArray(s.length / 2) { s.substring(it * 2, it * 2 + 2).toInt(16).toByte() }
}

private enum class DpadZone { NONE, UP, RIGHT, DOWN, LEFT, CENTER }

private class DpadWheelView(context: Context, private val onZoneTap: (DpadZone) -> Unit) : View(context) {
    private var sliceFill = Color.parseColor("#1D222E")
    private var sliceStroke = Color.parseColor("#2B3242")
    private var pressedSliceFill = Color.parseColor("#2D3648")
    private var centerFill = Color.parseColor("#E2E8F0")
    private var centerStroke = Color.parseColor("#94A3B8")
    private var centerTextColor = Color.parseColor("#0F172A")
    private var arrowColor = Color.parseColor("#F8FAFC")
    private var activeZone = DpadZone.NONE
    private val outerRect = RectF()
    private val innerRect = RectF()
    private val slicePaths = Array(4) { Path() }
    private val fillPaint = Paint(Paint.ANTI_ALIAS_FLAG).apply { style = Paint.Style.FILL }
    private val strokePaint = Paint(Paint.ANTI_ALIAS_FLAG).apply { style = Paint.Style.STROKE }
    private val glyphPaint = Paint(Paint.ANTI_ALIAS_FLAG).apply { textAlign = Paint.Align.CENTER; typeface = Typeface.DEFAULT_BOLD }

    fun applyColors(sliceFill: Int, sliceStroke: Int, centerFill: Int, centerStroke: Int, centerTextColor: Int, arrowColor: Int) {
        this.sliceFill = sliceFill; this.sliceStroke = sliceStroke
        this.pressedSliceFill = lighten(sliceFill, 1.24f)
        this.centerFill = centerFill; this.centerStroke = centerStroke
        this.centerTextColor = centerTextColor; this.arrowColor = arrowColor
        invalidate()
    }

    private fun lighten(color: Int, factor: Float): Int = Color.rgb(
        (Color.red(color) * factor).toInt().coerceIn(0, 255),
        (Color.green(color) * factor).toInt().coerceIn(0, 255),
        (Color.blue(color) * factor).toInt().coerceIn(0, 255)
    )

    override fun onMeasure(widthMeasureSpec: Int, heightMeasureSpec: Int) {
        val w = MeasureSpec.getSize(widthMeasureSpec); val h = MeasureSpec.getSize(heightMeasureSpec)
        val side = when { w > 0 && h > 0 -> min(w, h); w > 0 -> w; h > 0 -> h; else -> (240 * resources.displayMetrics.density).toInt() }
        val exact = MeasureSpec.makeMeasureSpec(side, MeasureSpec.EXACTLY)
        setMeasuredDimension(exact, exact)
    }

    override fun onSizeChanged(w: Int, h: Int, oldw: Int, oldh: Int) {
        super.onSizeChanged(w, h, oldw, oldh)
        if (w <= 0 || h <= 0) return
        val cx = w / 2f; val cy = h / 2f; val outerR = min(cx, cy) - 4f; val innerR = outerR * 0.34f
        outerRect.set(cx - outerR, cy - outerR, cx + outerR, cy + outerR)
        innerRect.set(cx - innerR, cy - innerR, cx + innerR, cy + innerR)
        val starts = floatArrayOf(-45f, 45f, 135f, 225f)
        for (i in 0 until 4) {
            slicePaths[i].apply { reset(); arcTo(outerRect, starts[i], 90f, true); arcTo(innerRect, starts[i] + 90f, -90f, false); close() }
        }
    }

    private fun zoneAt(x: Float, y: Float): DpadZone {
        val cx = width / 2f; val cy = height / 2f; val outerR = min(cx, cy) - 4f; val innerR = outerR * 0.34f
        val dist = hypot((x - cx).toDouble(), (y - cy).toDouble())
        if (dist > outerR) return DpadZone.NONE
        if (dist <= innerR) return DpadZone.CENTER
        var deg = Math.toDegrees(atan2((y - cy).toDouble(), (x - cx).toDouble())).toFloat()
        if (deg < 0f) deg += 360f
        return when { deg >= 315f || deg < 45f -> DpadZone.RIGHT; deg < 135f -> DpadZone.DOWN; deg < 225f -> DpadZone.LEFT; else -> DpadZone.UP }
    }

    override fun onDraw(canvas: Canvas) {
        super.onDraw(canvas)
        if (width <= 0 || height <= 0) return
        val cx = width / 2f; val cy = height / 2f; val outerR = min(cx, cy) - 4f; val innerR = outerR * 0.34f
        strokePaint.strokeWidth = maxOf(2f, outerR * 0.015f); strokePaint.color = sliceStroke
        val zones = arrayOf(DpadZone.RIGHT, DpadZone.DOWN, DpadZone.LEFT, DpadZone.UP)
        for (i in 0 until 4) {
            fillPaint.color = if (activeZone == zones[i]) pressedSliceFill else sliceFill
            canvas.drawPath(slicePaths[i], fillPaint); canvas.drawPath(slicePaths[i], strokePaint)
        }
        val midR = (outerR + innerR) * 0.52f
        glyphPaint.color = arrowColor; glyphPaint.textSize = outerR * 0.14f
        val offsetY = (glyphPaint.descent() + glyphPaint.ascent()) / 2f
        for ((sym, deg) in arrayOf("▲" to 270.0, "▶" to 0.0, "▼" to 90.0, "◀" to 180.0)) {
            val rad = Math.toRadians(deg)
            canvas.drawText(sym, cx + (midR * cos(rad)).toFloat(), cy + (midR * sin(rad)).toFloat() - offsetY, glyphPaint)
        }
        fillPaint.color = if (activeZone == DpadZone.CENTER) lighten(centerFill, 0.9f) else centerFill
        strokePaint.color = centerStroke
        canvas.drawCircle(cx, cy, innerR, fillPaint); canvas.drawCircle(cx, cy, innerR, strokePaint)
        glyphPaint.color = centerTextColor; glyphPaint.textSize = innerR * 0.5f
        canvas.drawText("OK", cx, cy - (glyphPaint.descent() + glyphPaint.ascent()) / 2f, glyphPaint)
    }

    private fun animateTap() { animate().cancel(); scaleX = 0.95f; scaleY = 0.95f; animate().scaleX(1f).scaleY(1f).setDuration(85L).start() }

    @SuppressLint("ClickableViewAccessibility")
    override fun onTouchEvent(event: MotionEvent): Boolean {
        when (event.actionMasked) {
            MotionEvent.ACTION_DOWN, MotionEvent.ACTION_MOVE -> {
                val z = zoneAt(event.x, event.y)
                if (z != activeZone) {
                    activeZone = z
                    if (event.actionMasked == MotionEvent.ACTION_DOWN && z != DpadZone.NONE) { scaleX = 0.95f; scaleY = 0.95f }
                    invalidate()
                }
                return true
            }
            MotionEvent.ACTION_UP -> {
                val z = zoneAt(event.x, event.y)
                if (z != DpadZone.NONE) { animateTap(); onZoneTap(z) } else { scaleX = 1f; scaleY = 1f }
                activeZone = DpadZone.NONE; invalidate(); performClick(); return true
            }
            MotionEvent.ACTION_CANCEL -> { scaleX = 1f; scaleY = 1f; activeZone = DpadZone.NONE; invalidate(); return true }
        }
        return super.onTouchEvent(event)
    }
    override fun performClick(): Boolean = super.performClick()
}

private enum class StatusState {
    DISCONNECTED, ENTER_IP, PAIRING_START, ENTER_CODE, PAIRING_FAILED,
    CODE_LENGTH, CODE_REJECTED, PAIRED_CONNECTING, CONNECTING,
    CONNECT_FAILED, CONNECTED, LOST, PAIR_RESET, SEND_FAILED,
    SCANNING, SCAN_NO_WIFI, SCAN_FOUND, SCAN_NONE
}

private data class ColorPalette(
    val key: String, val bg: Int, val card: Int, val surface: Int,
    val btn: Int, val btnStroke: Int, val accent: Int, val accentStroke: Int, val accentText: Int = Color.WHITE
)

private val stringsMap = mapOf(
    "tr" to mapOf(
        "tabRemote" to "Kumanda", "tabConnect" to "Bağlantı", "power" to "Güç",
        "tvIp" to "TV IP Adresi", "scanTv" to "Ağda TV Ara", "settings" to "Ayarlar",
        "hapticLevel" to "Titreşim Şiddeti", "wheelSize" to "Orta Tuş Boyutu",
        "theme" to "Renk Paleti", "lang" to "Dil",
        "codeHint" to "6 haneli kod", "confirm" to "Onayla", "connect" to "Bağlan",
        "autoOn" to "Oto Bağlan: Açık", "autoOff" to "Oto Bağlan: Kapalı",
        "resetPair" to "Eşleştirmeyi Sıfırla", "contactUs" to "Bize Ulaşın",
        "vibOff" to "Kapalı", "vibLight" to "Hafif", "vibMed" to "Orta", "vibStrong" to "Güçlü",
        "sizeSmall" to "Küçük", "sizeMedium" to "Orta", "sizeLarge" to "Büyük",
        "palBlue" to "Mavi", "palEmerald" to "Zümrüt", "palPurple" to "Mor",
        "palAmber" to "Kehribar", "palBw" to "Siyah Beyaz", "palCrimson" to "Yakut",
        "palCyan" to "Camgöbeği", "palCoral" to "Mercan",
        "scanModalTitle" to "TV Cihazları", "scanSearching" to "Ağınızda TV cihazları aranıyor…",
        "scanTroubles" to "Bağlantı sorunları?",
        "scanTroublesTip" to "Telefon ve TV aynı Wi-Fi ağında olmalı ve cihaz izolasyonu kapalı olmalıdır. Bulunamazsa IP'yi elle girin.",
        "disconnect" to "Bağlantıyı Kes", "tvDeviceFallback" to "Android TV",
        StatusState.DISCONNECTED.name to "Bağlı değil", StatusState.ENTER_IP.name to "Önce TV'nin IP adresini yaz",
        StatusState.PAIRING_START.name to "Eşleştirme başlıyor…", StatusState.ENTER_CODE.name to "TV'deki 6 haneli kodu yazıp Onayla'ya bas",
        StatusState.PAIRING_FAILED.name to "Eşleştirme başarısız", StatusState.CODE_LENGTH.name to "Kod 6 karakter olmalı",
        StatusState.CODE_REJECTED.name to "Kod kabul edilmedi", StatusState.PAIRED_CONNECTING.name to "Eşleşti — Bağlanıyor…",
        StatusState.CONNECTING.name to "Bağlanıyor…", StatusState.CONNECT_FAILED.name to "Bağlanamadı",
        StatusState.CONNECTED.name to "Bağlandı", StatusState.LOST.name to "Bağlantı koptu",
        StatusState.PAIR_RESET.name to "Eşleştirme sıfırlandı", StatusState.SEND_FAILED.name to "Gönderilemedi",
        StatusState.SCANNING.name to "Ağda TV aranıyor…", StatusState.SCAN_NO_WIFI.name to "Yerel Wi-Fi ağı bulunamadı",
        StatusState.SCAN_FOUND.name to "TV bulundu", StatusState.SCAN_NONE.name to "Ağda TV bulunamadı"
    ),
    "en" to mapOf(
        "tabRemote" to "Remote", "tabConnect" to "Connection", "power" to "Power",
        "tvIp" to "TV IP Address", "scanTv" to "Find TV on Network", "settings" to "Settings",
        "hapticLevel" to "Haptic Strength", "wheelSize" to "Center Wheel Size",
        "theme" to "Color Palette", "lang" to "Language",
        "codeHint" to "6-digit code", "confirm" to "Confirm", "connect" to "Connect",
        "autoOn" to "Auto Connect: On", "autoOff" to "Auto Connect: Off",
        "resetPair" to "Reset Pairing", "contactUs" to "Contact Us",
        "vibOff" to "Off", "vibLight" to "Light", "vibMed" to "Medium", "vibStrong" to "Strong",
        "sizeSmall" to "Small", "sizeMedium" to "Medium", "sizeLarge" to "Large",
        "palBlue" to "Blue", "palEmerald" to "Emerald", "palPurple" to "Purple",
        "palAmber" to "Amber", "palBw" to "Black & White", "palCrimson" to "Crimson",
        "palCyan" to "Cyan", "palCoral" to "Coral",
        "scanModalTitle" to "TV Devices", "scanSearching" to "Searching for TV devices on your network…",
        "scanTroubles" to "Connection troubles?",
        "scanTroublesTip" to "Keep phone and TV on the same Wi-Fi without AP isolation, or enter the TV IP manually.",
        "disconnect" to "Disconnect", "tvDeviceFallback" to "Android TV",
        StatusState.DISCONNECTED.name to "Disconnected", StatusState.ENTER_IP.name to "Enter the TV IP address first",
        StatusState.PAIRING_START.name to "Starting pairing…", StatusState.ENTER_CODE.name to "Enter the 6-digit code on TV and tap Confirm",
        StatusState.PAIRING_FAILED.name to "Pairing failed", StatusState.CODE_LENGTH.name to "Code must be 6 characters",
        StatusState.CODE_REJECTED.name to "Code rejected", StatusState.PAIRED_CONNECTING.name to "Paired — Connecting…",
        StatusState.CONNECTING.name to "Connecting…", StatusState.CONNECT_FAILED.name to "Connection failed",
        StatusState.CONNECTED.name to "Connected", StatusState.LOST.name to "Connection lost",
        StatusState.PAIR_RESET.name to "Pairing reset", StatusState.SEND_FAILED.name to "Failed to send",
        StatusState.SCANNING.name to "Scanning network for TV…", StatusState.SCAN_NO_WIFI.name to "Local Wi-Fi network not found",
        StatusState.SCAN_FOUND.name to "TV found", StatusState.SCAN_NONE.name to "No TV found on network"
    ),
    "ru" to mapOf(
        "tabRemote" to "Пульт", "tabConnect" to "Подключение", "power" to "Питание",
        "tvIp" to "IP-адрес ТВ", "scanTv" to "Найти ТВ в сети", "settings" to "Настройки",
        "hapticLevel" to "Сила вибрации", "wheelSize" to "Размер круга",
        "theme" to "Палитра цветов", "lang" to "Язык",
        "codeHint" to "6-значный код", "confirm" to "ОК", "connect" to "Подключить",
        "autoOn" to "Автоподкл.: Вкл", "autoOff" to "Автоподкл.: Выкл",
        "resetPair" to "Сбросить пару", "contactUs" to "Связаться с нами",
        "vibOff" to "Выкл", "vibLight" to "Слабая", "vibMed" to "Средняя", "vibStrong" to "Сильная",
        "sizeSmall" to "Малый", "sizeMedium" to "Средний", "sizeLarge" to "Большой",
        "palBlue" to "Синяя", "palEmerald" to "Изумруд", "palPurple" to "Фиолетовая",
        "palAmber" to "Янтарная", "palBw" to "Чёрно-белая", "palCrimson" to "Рубиновая",
        "palCyan" to "Бирюзовая", "palCoral" to "Коралловая",
        "scanModalTitle" to "TV Устройства", "scanSearching" to "Поиск устройств ТВ в вашей сети…",
        "scanTroubles" to "Проблемы с подключением?",
        "scanTroublesTip" to "Убедитесь, что телефон и ТВ в одной сети Wi-Fi, либо введите IP вручную.",
        "disconnect" to "Отключить", "tvDeviceFallback" to "Android TV",
        StatusState.DISCONNECTED.name to "Не подключено", StatusState.ENTER_IP.name to "Сначала введите IP-адрес ТВ",
        StatusState.PAIRING_START.name to "Начинаем сопряжение…", StatusState.ENTER_CODE.name to "Введите 6-значный код с ТВ и нажмите ОК",
        StatusState.PAIRING_FAILED.name to "Ошибка сопряжения", StatusState.CODE_LENGTH.name to "Код должен быть из 6 символов",
        StatusState.CODE_REJECTED.name to "Код отклонён", StatusState.PAIRED_CONNECTING.name to "Сопряжено — Подключение…",
        StatusState.CONNECTING.name to "Подключение…", StatusState.CONNECT_FAILED.name to "Не удалось подключиться",
        StatusState.CONNECTED.name to "Подключено", StatusState.LOST.name to "Соединение потеряно",
        StatusState.PAIR_RESET.name to "Сопряжение сброшено", StatusState.SEND_FAILED.name to "Ошибка отправки",
        StatusState.SCANNING.name to "Поиск ТВ в сети…", StatusState.SCAN_NO_WIFI.name to "Локальная сеть Wi-Fi не найдена",
        StatusState.SCAN_FOUND.name to "ТВ найден", StatusState.SCAN_NONE.name to "ТВ в сети не найдены"
    ),
    "az" to mapOf(
        "tabRemote" to "Pult", "tabConnect" to "Bağlantı", "power" to "Güc",
        "tvIp" to "TV IP Ünvanı", "scanTv" to "Şəbəkədə TV Tap", "settings" to "Ayarlar",
        "hapticLevel" to "Titrəmə Gücü", "wheelSize" to "Orta Düymə Ölçüsü",
        "theme" to "Rəng Palitrası", "lang" to "Dil",
        "codeHint" to "6 rəqəmli kod", "confirm" to "Təsdiqlə", "connect" to "Qoşul",
        "autoOn" to "Avto Qoşul: Açıq", "autoOff" to "Avto Qoşul: Bağlı",
        "resetPair" to "Cütləşməni Sıfırla", "contactUs" to "Bizimlə Əlaqə",
        "vibOff" to "Bağlı", "vibLight" to "Yüngül", "vibMed" to "Orta", "vibStrong" to "Güclü",
        "sizeSmall" to "Kiçik", "sizeMedium" to "Orta", "sizeLarge" to "Böyük",
        "palBlue" to "Mavi", "palEmerald" to "Zümrüd", "palPurple" to "Bənövşəyi",
        "palAmber" to "Kəhrəba", "palBw" to "Ağ-Qara", "palCrimson" to "Yaqut",
        "palCyan" to "Firuzəyi", "palCoral" to "Mərcan",
        "scanModalTitle" to "TV Cihazları", "scanSearching" to "Şəbəkənizdə TV cihazları axtarılır…",
        "scanTroubles" to "Bağlantı problemləri?",
        "scanTroublesTip" to "Telefon və TV eyni Wi-Fi şəbəkəsində olmalıdır; tapılmasa IP ünvanını əl ilə daxil edin.",
        "disconnect" to "Ayır", "tvDeviceFallback" to "Android TV",
        StatusState.DISCONNECTED.name to "Qoşulu deyil", StatusState.ENTER_IP.name to "Əvvəlcə TV-nin IP ünvanını yaz",
        StatusState.PAIRING_START.name to "Cütləşmə başlayır…", StatusState.ENTER_CODE.name to "TV-dəki 6 rəqəmli kodu yazıb Təsdiqlə bas",
        StatusState.PAIRING_FAILED.name to "Cütləşmə uğursuz oldu", StatusState.CODE_LENGTH.name to "Kod 6 simvol olmalıdır",
        StatusState.CODE_REJECTED.name to "Kod qəbul edilmədi", StatusState.PAIRED_CONNECTING.name to "Cütləşdi — Qoşulur…",
        StatusState.CONNECTING.name to "Qoşulur…", StatusState.CONNECT_FAILED.name to "Qoşulmaq olmadı",
        StatusState.CONNECTED.name to "Qoşuldu", StatusState.LOST.name to "Bağlantı kəsildi",
        StatusState.PAIR_RESET.name to "Cütləşmə sıfırlandı", StatusState.SEND_FAILED.name to "Göndərilə bilmədi",
        StatusState.SCANNING.name to "Şəbəkədə TV axtarılır…", StatusState.SCAN_NO_WIFI.name to "Yerli Wi-Fi şəbəkəsi tapılmadı",
        StatusState.SCAN_FOUND.name to "TV tapıldı", StatusState.SCAN_NONE.name to "Şəbəkədə TV tapılmadı"
    ),
    "zh" to mapOf(
        "tabRemote" to "遥控器", "tabConnect" to "连接", "power" to "电源",
        "tvIp" to "电视 IP 地址", "scanTv" to "搜索局域网电视", "settings" to "设置",
        "hapticLevel" to "震动强度", "wheelSize" to "中心转盘大小",
        "theme" to "配色方案", "lang" to "语言",
        "codeHint" to "6 位验证码", "confirm" to "确认", "connect" to "连接",
        "autoOn" to "自动连接：开", "autoOff" to "自动连接：关",
        "resetPair" to "重置配对", "contactUs" to "联系我们",
        "vibOff" to "关闭", "vibLight" to "轻微", "vibMed" to "适中", "vibStrong" to "强烈",
        "sizeSmall" to "小", "sizeMedium" to "中", "sizeLarge" to "大",
        "palBlue" to "蓝色", "palEmerald" to "祖母绿", "palPurple" to "紫色",
        "palAmber" to "琥珀色", "palBw" to "黑白", "palCrimson" to "深红",
        "palCyan" to "青色", "palCoral" to "珊瑚色",
        "scanModalTitle" to "电视设备", "scanSearching" to "正在您的网络中搜索电视设备…",
        "scanTroubles" to "连接遇到问题？",
        "scanTroublesTip" to "请确保手机和电视处于同一 Wi-Fi 网络且未开启设备隔离，否则请手动输入 IP。",
        "disconnect" to "断开连接", "tvDeviceFallback" to "Android TV",
        StatusState.DISCONNECTED.name to "未连接", StatusState.ENTER_IP.name to "请先输入电视 IP 地址",
        StatusState.PAIRING_START.name to "正在开始配对…", StatusState.ENTER_CODE.name to "输入电视上的 6 位验证码并点击确认",
        StatusState.PAIRING_FAILED.name to "配对失败", StatusState.CODE_LENGTH.name to "验证码必须为 6 位",
        StatusState.CODE_REJECTED.name to "验证码被拒绝", StatusState.PAIRED_CONNECTING.name to "已配对 — 正在连接…",
        StatusState.CONNECTING.name to "正在连接…", StatusState.CONNECT_FAILED.name to "连接失败",
        StatusState.CONNECTED.name to "已连接", StatusState.LOST.name to "连接已断开",
        StatusState.PAIR_RESET.name to "已重置配对", StatusState.SEND_FAILED.name to "发送失败",
        StatusState.SCANNING.name to "正在搜索电视…", StatusState.SCAN_NO_WIFI.name to "未找到局域网 Wi-Fi",
        StatusState.SCAN_FOUND.name to "已找到电视", StatusState.SCAN_NONE.name to "网络中未找到电视"
    ),
    "es" to mapOf(
        "tabRemote" to "Mando", "tabConnect" to "Conexión", "power" to "Encender",
        "tvIp" to "Dirección IP de TV", "scanTv" to "Buscar TV en red", "settings" to "Ajustes",
        "hapticLevel" to "Intensidad háptica", "wheelSize" to "Tamaño central",
        "theme" to "Paleta de color", "lang" to "Idioma",
        "codeHint" to "Código de 6 dígitos", "confirm" to "Confirmar", "connect" to "Conectar",
        "autoOn" to "Autoconexión: Activada", "autoOff" to "Autoconexión: Desactivada",
        "resetPair" to "Restablecer vínculo", "contactUs" to "Contáctanos",
        "vibOff" to "Apagado", "vibLight" to "Suave", "vibMed" to "Media", "vibStrong" to "Fuerte",
        "sizeSmall" to "Pequeño", "sizeMedium" to "Mediano", "sizeLarge" to "Grande",
        "palBlue" to "Azul", "palEmerald" to "Esmeralda", "palPurple" to "Morado",
        "palAmber" to "Ámbar", "palBw" to "Blanco y negro", "palCrimson" to "Carmesí",
        "palCyan" to "Cian", "palCoral" to "Coral",
        "scanModalTitle" to "Dispositivos TV", "scanSearching" to "Buscando dispositivos TV en tu red…",
        "scanTroubles" to "¿Problemas de conexión?",
        "scanTroublesTip" to "Conecta móvil y TV al mismo Wi-Fi sin aislamiento de clientes o escribe la IP manualmente.",
        "disconnect" to "Desconectar", "tvDeviceFallback" to "Android TV",
        StatusState.DISCONNECTED.name to "Desconectado", StatusState.ENTER_IP.name to "Escribe primero la IP del TV",
        StatusState.PAIRING_START.name to "Iniciando vinculación…", StatusState.ENTER_CODE.name to "Escribe el código de 6 dígitos en TV y pulsa Confirmar",
        StatusState.PAIRING_FAILED.name to "Error al vincular", StatusState.CODE_LENGTH.name to "El código debe tener 6 caracteres",
        StatusState.CODE_REJECTED.name to "Código rechazado", StatusState.PAIRED_CONNECTING.name to "Vinculado — Conectando…",
        StatusState.CONNECTING.name to "Conectando…", StatusState.CONNECT_FAILED.name to "No se pudo conectar",
        StatusState.CONNECTED.name to "Conectado", StatusState.LOST.name to "Conexión perdida",
        StatusState.PAIR_RESET.name to "Vinculación restablecida", StatusState.SEND_FAILED.name to "Error al enviar",
        StatusState.SCANNING.name to "Buscando TV en la red…", StatusState.SCAN_NO_WIFI.name to "No se encontró red Wi-Fi local",
        StatusState.SCAN_FOUND.name to "TV encontrado", StatusState.SCAN_NONE.name to "No se encontró ningún TV en la red"
    ),
    "ar" to mapOf(
        "tabRemote" to "التحكم", "tabConnect" to "الاتصال", "power" to "الطاقة",
        "tvIp" to "عنوان IP للتلفاز", "scanTv" to "بحث عن تلفاز بالشبكة", "settings" to "الإعدادات",
        "hapticLevel" to "قوة الاهتزاز", "wheelSize" to "حجم القرص الأوسط",
        "theme" to "لوحة الألوان", "lang" to "اللغة",
        "codeHint" to "رمز من 6 أرقام", "confirm" to "تأكيد", "connect" to "اتصال",
        "autoOn" to "اتصال تلقائي: تشغيل", "autoOff" to "اتصال تلقائي: إيقاف",
        "resetPair" to "إعادة ضبط الإقران", "contactUs" to "تواصل معنا",
        "vibOff" to "إيقاف", "vibLight" to "خفيف", "vibMed" to "متوسط", "vibStrong" to "قوي",
        "sizeSmall" to "صغير", "sizeMedium" to "متوسط", "sizeLarge" to "كبير",
        "palBlue" to "أزرق", "palEmerald" to "زمردي", "palPurple" to "بنفسجي",
        "palAmber" to "كهرماني", "palBw" to "أبيض وأسود", "palCrimson" to "قرمزي",
        "palCyan" to "سماوي", "palCoral" to "مرجاني",
        "scanModalTitle" to "أجهزة التلفاز", "scanSearching" to "جارٍ البحث عن أجهزة التلفاز في شبكتك…",
        "scanTroubles" to "مشاكل في الاتصال؟",
        "scanTroublesTip" to "تأكد أن الهاتف والتلفاز على نفس شبكة Wi-Fi أو أدخل عنوان IP يدويًا.",
        "disconnect" to "قطع الاتصال", "tvDeviceFallback" to "Android TV",
        StatusState.DISCONNECTED.name to "غير متصل", StatusState.ENTER_IP.name to "أدخل عنوان IP للتلفاز أولاً",
        StatusState.PAIRING_START.name to "بدء الإقران…", StatusState.ENTER_CODE.name to "أدخل الرمز المكون من 6 أرقام على التلفاز ثم اضغط تأكيد",
        StatusState.PAIRING_FAILED.name to "فشل الإقران", StatusState.CODE_LENGTH.name to "يجب أن يتكون الرمز من 6 أحرف",
        StatusState.CODE_REJECTED.name to "تم رفض الرمز", StatusState.PAIRED_CONNECTING.name to "تم الإقران — جارٍ الاتصال…",
        StatusState.CONNECTING.name to "جارٍ الاتصال…", StatusState.CONNECT_FAILED.name to "تعذر الاتصال",
        StatusState.CONNECTED.name to "متصل", StatusState.LOST.name to "انقطع الاتصال",
        StatusState.PAIR_RESET.name to "تمت إعادة ضبط الإقران", StatusState.SEND_FAILED.name to "تعذر الإرسال",
        StatusState.SCANNING.name to "جارٍ البحث عن التلفاز في الشبكة…", StatusState.SCAN_NO_WIFI.name to "لم يتم العثور على شبكة Wi-Fi محلية",
        StatusState.SCAN_FOUND.name to "تم العثور على التلفاز", StatusState.SCAN_NONE.name to "لم يتم العثور على تلفاز في الشبكة"
    ),
    "hi" to mapOf(
        "tabRemote" to "रिमोट", "tabConnect" to "कनेक्शन", "power" to "पावर",
        "tvIp" to "टीवी IP पता", "scanTv" to "नेटवर्क में टीवी खोजें", "settings" to "सेटिंग्स",
        "hapticLevel" to "कंपन तीव्रता", "wheelSize" to "बीच के चक्र का आकार",
        "theme" to "रंग पैलेट", "lang" to "भाषा",
        "codeHint" to "6 अंकों का कोड", "confirm" to "पुष्टि करें", "connect" to "कनेक्ट करें",
        "autoOn" to "ऑटो कनेक्ट: चालू", "autoOff" to "ऑटो कनेक्ट: बंद",
        "resetPair" to "पेयरिंग रीसेट करें", "contactUs" to "संपर्क करें",
        "vibOff" to "बंद", "vibLight" to "हल्का", "vibMed" to "मध्यम", "vibStrong" to "तेज़",
        "sizeSmall" to "छोटा", "sizeMedium" to "मध्यम", "sizeLarge" to "बड़ा",
        "palBlue" to "नीला", "palEmerald" to "पन्ना", "palPurple" to "बैंगनी",
        "palAmber" to "अंबर", "palBw" to "श्वेत-श्याम", "palCrimson" to "गहरा लाल",
        "palCyan" to "सियान", "palCoral" to "कोरल",
        "scanModalTitle" to "टीवी डिवाइस", "scanSearching" to "आपके नेटवर्क में टीवी डिवाइस खोजे जा रहे हैं…",
        "scanTroubles" to "कनेक्शन में समस्या?",
        "scanTroublesTip" to "फ़ोन और टीवी को एक ही Wi-Fi पर रखें या IP मैन्युअल रूप से दर्ज करें।",
        "disconnect" to "डिस्कनेक्ट करें", "tvDeviceFallback" to "Android TV",
        StatusState.DISCONNECTED.name to "डिस्कनेक्टेड", StatusState.ENTER_IP.name to "पहले टीवी का IP पता दर्ज करें",
        StatusState.PAIRING_START.name to "पेयरिंग शुरू हो रही है…", StatusState.ENTER_CODE.name to "टीवी पर 6 अंकों का कोड दर्ज करें और पुष्टि करें दबाएं",
        StatusState.PAIRING_FAILED.name to "पेयरिंग विफल रही", StatusState.CODE_LENGTH.name to "कोड 6 अक्षरों का होना चाहिए",
        StatusState.CODE_REJECTED.name to "कोड अस्वीकार किया गया", StatusState.PAIRED_CONNECTING.name to "पेयर हो गया — कनेक्ट हो रहा है…",
        StatusState.CONNECTING.name to "कनेक्ट हो रहा है…", StatusState.CONNECT_FAILED.name to "कनेक्ट नहीं हो सका",
        StatusState.CONNECTED.name to "कनेक्टेड", StatusState.LOST.name to "कनेक्शन टूट गया",
        StatusState.PAIR_RESET.name to "पेयरिंग रीसेट हो गई", StatusState.SEND_FAILED.name to "भेजा नहीं जा सका",
        StatusState.SCANNING.name to "नेटवर्क में टीवी खोजा जा रहा है…", StatusState.SCAN_NO_WIFI.name to "लोकल Wi-Fi नेटवर्क नहीं मिला",
        StatusState.SCAN_FOUND.name to "टीवी मिल गया", StatusState.SCAN_NONE.name to "नेटवर्क में कोई टीवी नहीं मिला"
    )
)

class MainActivity : Activity() {
    private val fastIo = Executors.newCachedThreadPool()
    private var identity: Identity? = null
    private var remote: Conn? = null
    @Volatile private var ready = false
    @Volatile private var reconnecting = false
    @Volatile private var manualDisconnect = false
    @Volatile private var scanToken = 0
    private var pairConn: Conn? = null
    private var pairServerCert: X509Certificate? = null
    private var host = ""
    private var connectedHost: String? = null
    @Volatile private var hapticStrength = 2
    @Volatile private var wheelSizeMode = 1
    @Volatile private var autoConnectEnabled = true
    private var currentLang = "tr"
    private var settingsOpen = false
    private var vibDropdownOpen = false
    private var sizeDropdownOpen = false
    private var paletteDropdownOpen = false
    private var langDropdownOpen = false
    private var scanModalOpen = false
    private var scanInProgress = false
    private var pulseAnim: ObjectAnimator? = null
    private var scanTroublesVisible = false
    private var lastStatusState = StatusState.DISCONNECTED
    private var lastStatusDetail: String? = null
    private var lastStatusDotColor = Color.parseColor("#64748B")
    private val instagramUrl = "https://www.instagram.com/erew02?cnvx=MTg4bDEyNnYzZ3dmOA=="

    private val palettes = listOf(
        ColorPalette("palBlue", Color.parseColor("#0B0D12"), Color.parseColor("#141821"), Color.parseColor("#10141C"), Color.parseColor("#1D222E"), Color.parseColor("#2B3242"), Color.parseColor("#2563EB"), Color.parseColor("#60A5FA")),
        ColorPalette("palEmerald", Color.parseColor("#09110E"), Color.parseColor("#111F1A"), Color.parseColor("#0D1814"), Color.parseColor("#182B24"), Color.parseColor("#264237"), Color.parseColor("#059669"), Color.parseColor("#34D399")),
        ColorPalette("palPurple", Color.parseColor("#0E0B14"), Color.parseColor("#191424"), Color.parseColor("#13101C"), Color.parseColor("#241D33"), Color.parseColor("#362C4D"), Color.parseColor("#7C3AED"), Color.parseColor("#A78BFA")),
        ColorPalette("palAmber", Color.parseColor("#120E09"), Color.parseColor("#201810"), Color.parseColor("#18120C"), Color.parseColor("#2E2216"), Color.parseColor("#453321"), Color.parseColor("#D97706"), Color.parseColor("#FBBF24")),
        ColorPalette("palBw", Color.parseColor("#000000"), Color.parseColor("#121212"), Color.parseColor("#0A0A0A"), Color.parseColor("#1E1E1E"), Color.parseColor("#4A4A4A"), Color.parseColor("#FFFFFF"), Color.parseColor("#FFFFFF"), Color.parseColor("#000000")),
        ColorPalette("palCrimson", Color.parseColor("#13090B"), Color.parseColor("#221115"), Color.parseColor("#190D10"), Color.parseColor("#33181E"), Color.parseColor("#4D232C"), Color.parseColor("#DC2626"), Color.parseColor("#F87171")),
        ColorPalette("palCyan", Color.parseColor("#081114"), Color.parseColor("#0F1E24"), Color.parseColor("#0B161B"), Color.parseColor("#162B33"), Color.parseColor("#22414D"), Color.parseColor("#0891B2"), Color.parseColor("#22D3EE")),
        ColorPalette("palCoral", Color.parseColor("#140B0E"), Color.parseColor("#241419"), Color.parseColor("#1A0E12"), Color.parseColor("#341C24"), Color.parseColor("#4D2935"), Color.parseColor("#E11D48"), Color.parseColor("#FB7185"))
    )
    private val vibLevels = listOf(0 to "vibOff", 1 to "vibLight", 2 to "vibMed", 3 to "vibStrong")
    private val wheelSizes = listOf(0 to ("sizeSmall" to 214), 1 to ("sizeMedium" to 252), 2 to ("sizeLarge" to 292))
    private val languages = listOf("tr" to "Türkçe", "en" to "English", "ru" to "Русский", "az" to "Azərbaycan", "zh" to "中文", "es" to "Español", "ar" to "العربية", "hi" to "हिन्दी")

    private var paletteIndex = 0
    private var cBg = palettes[0].bg; private var cCard = palettes[0].card; private var cSurface = palettes[0].surface
    private var cBtn = palettes[0].btn; private var cBtnStroke = palettes[0].btnStroke
    private var cAccent = palettes[0].accent; private var cAccentStroke = palettes[0].accentStroke; private var cAccentText = palettes[0].accentText
    private val cRedSoft = Color.parseColor("#2A1418"); private val cRedSolid = Color.parseColor("#EF4444"); private val cRedStroke = Color.parseColor("#F87171")
    private val cGreen = Color.parseColor("#22C55E"); private val cMuted = Color.parseColor("#64748B")
    private val cText = Color.parseColor("#F8FAFC"); private val cSubtext = Color.parseColor("#CBD5E1")

    private lateinit var rootView: LinearLayout
    private lateinit var topBarView: LinearLayout
    private lateinit var dpadWheelView: DpadWheelView
    private lateinit var powerBtnView: Button
    private lateinit var remoteHeaderTvName: TextView
    private lateinit var remoteHeaderDot: View
    private lateinit var remoteHeaderSettingsBtn: Button
    private lateinit var connectCardView: LinearLayout
    private lateinit var settingsSectionView: LinearLayout
    private lateinit var settingsCardView: LinearLayout
    private lateinit var tvIpTitleView: TextView
    private lateinit var scanTvBtnView: Button
    private lateinit var settingsTitleView: TextView
    private lateinit var openSettingsBtnView: Button
    private lateinit var connectBtnView: Button
    private lateinit var resetPairBtnView: Button
    private lateinit var contactUsBtnView: Button
    private lateinit var confirmPairBtnView: Button
    private lateinit var statusDot: View
    private lateinit var status: TextView
    private lateinit var ipBox: EditText
    private lateinit var codeBox: EditText
    private lateinit var codeRow: LinearLayout
    private lateinit var autoConnectBtn: Button

    private lateinit var vibHeaderRow: LinearLayout; private lateinit var vibHeaderLabel: TextView; private lateinit var vibHeaderValue: TextView; private lateinit var vibOptionsContainer: LinearLayout
    private lateinit var sizeHeaderRow: LinearLayout; private lateinit var sizeHeaderLabel: TextView; private lateinit var sizeHeaderValue: TextView; private lateinit var sizeOptionsContainer: LinearLayout
    private lateinit var paletteHeaderRow: LinearLayout; private lateinit var paletteHeaderLabel: TextView; private lateinit var paletteHeaderValue: TextView; private lateinit var paletteOptionsContainer: LinearLayout
    private lateinit var langHeaderRow: LinearLayout; private lateinit var langHeaderLabel: TextView; private lateinit var langHeaderValue: TextView; private lateinit var langOptionsContainer: LinearLayout

    private lateinit var scanBackdropView: FrameLayout; private lateinit var scanDialogCardView: LinearLayout; private lateinit var scanIconBadge: TextView
    private lateinit var scanTitleView: TextView; private lateinit var scanCloseBtn: Button; private lateinit var scanIndicatorView: View
    private lateinit var scanMessageView: TextView; private lateinit var scanResultsContainer: LinearLayout
    private lateinit var scanTroublesBtn: TextView; private lateinit var scanTroublesTipView: TextView

    private var dp = 1f; private var sp = 1f; private var currentScreen = 0
    private var step = "başlangıç"

    private fun findCycle(root: View): String? {
        val path = ArrayList<View>()
        fun walk(v: View): String? {
            fun nm(x: View) = x.javaClass.simpleName + "#" + System.identityHashCode(x)
            if (path.any { it === v }) return "DÖNGÜ: " + path.joinToString(" > ") { nm(it) } + " > " + nm(v)
            if (path.size > 60) return "ÇOK DERİN: " + path.takeLast(5).joinToString(" > ") { nm(it) }
            path.add(v)
            if (v is ViewGroup) for (i in 0 until v.childCount) walk(v.getChildAt(i))?.let { return it }
            path.removeAt(path.size - 1)
            return null
        }
        return walk(root)
    }

    private val navBtns = ArrayList<Button>(); private val roundActionBtns = ArrayList<Button>()
    private val vibRows = ArrayList<Pair<Int, LinearLayout>>(); private val sizeRows = ArrayList<Pair<Int, LinearLayout>>()
    private val paletteRows = ArrayList<Pair<Int, LinearLayout>>(); private val langRows = ArrayList<Pair<String, LinearLayout>>()
    private val screens = ArrayList<View>(); private val scannedIps = ArrayList<String>()

    private fun t(key: String): String = stringsMap[currentLang]?.get(key) ?: stringsMap.getValue("tr").getValue(key)
    private fun px(v: Int) = (v * dp).toInt().coerceAtLeast(1)
    private fun scaledSp(v: Float) = v * (sp / dp).coerceIn(0.85f, 1.3f)
    private fun lp(w: Int, h: Int, weight: Float = 0f, l: Int = 0, top: Int = 0, r: Int = 0, b: Int = 0) =
        LinearLayout.LayoutParams(w, h, weight).apply { setMargins(px(l), px(top), px(r), px(b)) }

    private fun applyPressAnim(v: View) {
        v.setOnTouchListener { view, event ->
            when (event.actionMasked) {
                MotionEvent.ACTION_DOWN -> { view.animate().cancel(); view.scaleX = 0.94f; view.scaleY = 0.94f }
                MotionEvent.ACTION_UP, MotionEvent.ACTION_CANCEL -> view.animate().scaleX(1f).scaleY(1f).setDuration(85L).start()
            }
            false
        }
    }

    @Suppress("DEPRECATION")
    private fun tap(levelOverride: Int? = null, v: View? = null) {
        val lvl = levelOverride ?: hapticStrength; if (lvl <= 0) return
        val target = v ?: window.decorView
        val durationMs = if (lvl == 1) 14L else if (lvl == 2) 28L else 48L
        val amplitude = if (lvl == 1) 60 else if (lvl == 2) 150 else 255
        try {
            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S) {
                (getSystemService(Context.VIBRATOR_MANAGER_SERVICE) as VibratorManager).defaultVibrator.vibrate(VibrationEffect.createOneShot(durationMs, amplitude))
            } else if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
                (getSystemService(Context.VIBRATOR_SERVICE) as Vibrator).vibrate(VibrationEffect.createOneShot(durationMs, amplitude))
            } else target.performHapticFeedback(if (lvl >= 3) HapticFeedbackConstants.LONG_PRESS else HapticFeedbackConstants.VIRTUAL_KEY)
        } catch (_: Exception) { target.performHapticFeedback(HapticFeedbackConstants.VIRTUAL_KEY) }
    }

    private fun makeShapeBg(fill: Int, stroke: Int, oval: Boolean, radiusDp: Int = 24): RippleDrawable {
        val shape = GradientDrawable().apply {
            shape = if (oval) GradientDrawable.OVAL else GradientDrawable.RECTANGLE
            if (!oval) cornerRadius = px(radiusDp).toFloat()
            setColor(fill); setStroke(px(2), stroke)
        }
        return RippleDrawable(ColorStateList.valueOf(Color.parseColor("#38FFFFFF")), shape, null)
    }

    private fun makeCardBg(fill: Int = cSurface, stroke: Int = cBtnStroke, radiusDp: Int = 26) = GradientDrawable().apply {
        shape = GradientDrawable.RECTANGLE; cornerRadius = px(radiusDp).toFloat(); setColor(fill); setStroke(px(1), stroke)
    }

    private fun styleBtn(b: Button, fill: Int, stroke: Int, textColor: Int, sizeSp: Float, radiusDp: Int = 24, circle: Boolean = false) {
        b.background = makeShapeBg(fill, stroke, circle, radiusDp)
        b.setTextColor(textColor); b.typeface = Typeface.DEFAULT_BOLD; b.isAllCaps = false
        b.setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(sizeSp))
        b.setPadding(if (circle) 0 else px(8), 0, if (circle) 0 else px(8), 0)
        b.minWidth = 0; b.minimumWidth = 0; b.minHeight = 0; b.minimumHeight = 0
        applyPressAnim(b)
    }

    private fun createDropdownHeader(onToggle: () -> Unit): Triple<LinearLayout, TextView, TextView> {
        lateinit var labelTv: TextView; lateinit var valueTv: TextView
        val arrowTv = TextView(this).apply { typeface = Typeface.DEFAULT_BOLD; setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(12f)) }
        val row = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL
            isClickable = true; isFocusable = true; setPadding(px(14), px(13), px(14), px(13))
            layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT, 0f, 0, 8, 0, 4)
            labelTv = TextView(this@MainActivity).apply { typeface = Typeface.DEFAULT_BOLD; setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(14f)); layoutParams = lp(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f) }
            valueTv = TextView(this@MainActivity).apply { typeface = Typeface.DEFAULT_BOLD; setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(13.5f)); layoutParams = lp(LinearLayout.LayoutParams.WRAP_CONTENT, LinearLayout.LayoutParams.WRAP_CONTENT, 0f, 0, 0, 8, 0) }
            addView(labelTv); addView(valueTv); addView(arrowTv); tag = arrowTv; applyPressAnim(this)
            setOnClickListener { tap(v = this); onToggle() }
        }
        return Triple(row, labelTv, valueTv)
    }

    private fun optionRow(title: String, dotColor: Int?, onClick: () -> Unit) = LinearLayout(this).apply {
        orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL
        isClickable = true; isFocusable = true; setPadding(px(14), px(12), px(14), px(12))
        layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT, 0f, 0, 0, 0, 6)
        if (dotColor != null) addView(View(this@MainActivity).apply {
            layoutParams = lp(px(12), px(12), 0f, 0, 0, 10, 0)
            background = GradientDrawable().apply { shape = GradientDrawable.OVAL; setColor(dotColor) }
        })
        addView(TextView(this@MainActivity).apply { text = title; typeface = Typeface.DEFAULT_BOLD; setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(14f)); layoutParams = lp(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f) })
        addView(TextView(this@MainActivity).apply { typeface = Typeface.DEFAULT_BOLD; setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(13f)) })
        applyPressAnim(this); setOnClickListener { tap(v = this); onClick() }
    }

    private fun syncDropdownSection(
        open: Boolean, container: LinearLayout, headerRow: LinearLayout, labelTv: TextView,
        valueTv: TextView, titleKey: String, activeText: String, activeColor: Int,
        rows: List<Pair<*, LinearLayout>>, isSelected: (Any?) -> Boolean,
        rowStrokeFor: (Any?) -> Int, labelFor: (Any?) -> String?, textIdx: Int, markIdx: Int
    ) {
        headerRow.background = makeCardBg(if (open) cCard else cBtn, if (open) cAccentStroke else cBtnStroke, 16)
        labelTv.text = t(titleKey); labelTv.setTextColor(cText)
        valueTv.text = activeText; valueTv.setTextColor(activeColor)
        (headerRow.tag as? TextView)?.apply { text = if (open) "▲" else "▼"; setTextColor(cSubtext) }
        container.visibility = if (open) View.VISIBLE else View.GONE
        for ((key, rowView) in rows) {
            val sel = isSelected(key); val st = rowStrokeFor(key)
            rowView.background = makeCardBg(if (sel) cCard else cBtn, if (sel) st else cBtnStroke, 16)
            labelFor(key)?.let { (rowView.getChildAt(textIdx) as? TextView)?.text = it }
            (rowView.getChildAt(textIdx) as? TextView)?.setTextColor(if (sel) cText else cSubtext)
            (rowView.getChildAt(markIdx) as? TextView)?.apply { text = if (sel) "●" else ""; setTextColor(st) }
        }
    }

    private fun formatStatus(state: StatusState, detail: String?): String =
        t(state.name).let { if (!detail.isNullOrBlank()) "$it: $detail" else it }

    private fun updateRemoteHeaderIndicator() {
        val labelIp = connectedHost ?: host.ifBlank { ipBox.text.toString().trim() }
        remoteHeaderTvName.text = if (labelIp.isNotBlank()) labelIp else t("tvDeviceFallback")
        (remoteHeaderDot.background as? GradientDrawable)?.setColor(if (ready && remote != null) cGreen else cMuted)
    }

    private fun show(i: Int) {
        val target = i.coerceIn(0, (screens.size - 1).coerceAtLeast(0))
        currentScreen = target
        for (n in screens.indices) screens[n].visibility = if (n == target) View.VISIBLE else View.GONE
        if (target != 1 && settingsOpen) { settingsOpen = false; settingsSectionView.visibility = View.GONE }
        if (target == 0) updateRemoteHeaderIndicator()
        for (n in navBtns.indices) {
            val active = n == target
            navBtns[n].background = makeShapeBg(if (active) cAccent else cCard, if (active) cAccentStroke else cBtnStroke, false)
            navBtns[n].setTextColor(if (active) cAccentText else cSubtext)
        }
    }

    private fun refreshDropdowns() {
        val curPal = palettes[paletteIndex.coerceIn(0, palettes.lastIndex)]
        val activeVibKey = vibLevels.firstOrNull { it.first == hapticStrength }?.second ?: "vibMed"
        val activeSizeKey = wheelSizes.firstOrNull { it.first == wheelSizeMode }?.second?.first ?: "sizeMedium"
        val curLangLabel = languages.firstOrNull { it.first == currentLang }?.second ?: currentLang

        syncDropdownSection(vibDropdownOpen, vibOptionsContainer, vibHeaderRow, vibHeaderLabel, vibHeaderValue,
            "hapticLevel", t(activeVibKey), cAccentStroke, vibRows, { it == hapticStrength }, { cAccentStroke },
            { k -> t(vibLevels.firstOrNull { it.first == k }?.second ?: "vibOff") }, 0, 1)
        syncDropdownSection(sizeDropdownOpen, sizeOptionsContainer, sizeHeaderRow, sizeHeaderLabel, sizeHeaderValue,
            "wheelSize", t(activeSizeKey), cAccentStroke, sizeRows, { it == wheelSizeMode }, { cAccentStroke },
            { k -> t(wheelSizes.firstOrNull { it.first == k }?.second?.first ?: "sizeMedium") }, 0, 1)
        syncDropdownSection(paletteDropdownOpen, paletteOptionsContainer, paletteHeaderRow, paletteHeaderLabel, paletteHeaderValue,
            "theme", t(curPal.key), curPal.accentStroke, paletteRows, { it == paletteIndex },
            { k -> palettes[(k as? Int) ?: 0].accentStroke }, { k -> t(palettes[(k as? Int) ?: 0].key) }, 1, 2)
        syncDropdownSection(langDropdownOpen, langOptionsContainer, langHeaderRow, langHeaderLabel, langHeaderValue,
            "lang", curLangLabel, cAccentStroke, langRows, { it == currentLang }, { cAccentStroke }, { null }, 0, 1)
    }

    private fun applyTextsAndState() {
        if (navBtns.size >= 2) { navBtns[0].text = t("tabRemote"); navBtns[1].text = t("tabConnect") }
        powerBtnView.text = "⏻"; tvIpTitleView.text = t("tvIp"); scanTvBtnView.text = t("scanTv")
        openSettingsBtnView.text = "⚙ ${t("settings")}"; settingsTitleView.text = t("settings")
        codeBox.hint = t("codeHint"); confirmPairBtnView.text = t("confirm"); connectBtnView.text = t("connect")
        autoConnectBtn.text = t(if (autoConnectEnabled) "autoOn" else "autoOff")
        resetPairBtnView.text = t("resetPair"); contactUsBtnView.text = t("contactUs")
        status.text = formatStatus(lastStatusState, lastStatusDetail)
        (statusDot.background as? GradientDrawable)?.setColor(lastStatusDotColor)
        updateRemoteHeaderIndicator()
        scanTitleView.text = t("scanModalTitle"); scanTroublesBtn.text = t("scanTroubles"); scanTroublesTipView.text = t("scanTroublesTip")
        if (scanInProgress) scanMessageView.text = t("scanSearching")
        if (scanModalOpen && scannedIps.isNotEmpty()) rebuildFoundTvCards()
        refreshDropdowns()
    }

    private fun applyLanguage(lang: String) { currentLang = if (stringsMap.containsKey(lang)) lang else "tr"; applyTextsAndState() }

    private fun applyPalette(index: Int, switchTab: Boolean = false) {
        val p = palettes[index.coerceIn(0, palettes.lastIndex)]
        paletteIndex = index; cBg = p.bg; cCard = p.card; cSurface = p.surface; cBtn = p.btn; cBtnStroke = p.btnStroke
        cAccent = p.accent; cAccentStroke = p.accentStroke; cAccentText = p.accentText

        rootView.setBackgroundColor(cBg)
        topBarView.background = makeCardBg(cCard, cBtnStroke, 20)
        connectCardView.background = makeCardBg(cSurface, cBtnStroke, 28)
        settingsCardView.background = makeCardBg(cSurface, cBtnStroke, 28)
        dpadWheelView.applyColors(cBtn, cBtnStroke, Color.parseColor("#E2E8F0"), Color.parseColor("#94A3B8"), Color.parseColor("#0F172A"), cText)
        ipBox.background = makeCardBg(cCard, cBtnStroke, 18); codeBox.background = makeCardBg(cCard, cBtnStroke, 18)

        remoteHeaderTvName.setTextColor(cText)
        styleBtn(powerBtnView, cRedSoft, cRedStroke, cRedStroke, 20f, circle = true)
        styleBtn(remoteHeaderSettingsBtn, cBtn, cBtnStroke, cText, 18f, circle = true)
        for (btn in roundActionBtns) styleBtn(btn, cBtn, cBtnStroke, cText, 19f, circle = true)

        scanDialogCardView.background = makeCardBg(cCard, cBtnStroke, 26)
        (scanIndicatorView.background as? GradientDrawable)?.setColor(cAccentStroke)
        for (tv in listOf(scanIconBadge, scanTitleView)) tv.setTextColor(cText)
        for (tv in listOf(scanCloseBtn, scanMessageView, scanTroublesBtn, scanTroublesTipView)) tv.setTextColor(cSubtext)
        scanTroublesTipView.background = makeCardBg(cSurface, cBtnStroke, 14)

        styleBtn(scanTvBtnView, cBtn, cBtnStroke, cText, 14.5f, 18)
        styleBtn(openSettingsBtnView, if (settingsOpen) cAccent else cBtn, if (settingsOpen) cAccentStroke else cBtnStroke, if (settingsOpen) cAccentText else cText, 15f, 18)
        styleBtn(connectBtnView, cAccent, cAccentStroke, cAccentText, 16f, 18)
        styleBtn(confirmPairBtnView, cAccent, cAccentStroke, cAccentText, 15f, 18)
        styleBtn(autoConnectBtn, if (autoConnectEnabled) cBtn else cCard, cBtnStroke, if (autoConnectEnabled) cText else cSubtext, 14f, 16)
        styleBtn(resetPairBtnView, cRedSoft, cRedStroke, cText, 14f, 16)
        styleBtn(contactUsBtnView, cBtn, cAccentStroke, cText, 14.5f, 16)

        applyTextsAndState()
        if (switchTab) show(currentScreen)
        else for (n in navBtns.indices) {
            val active = n == currentScreen
            navBtns[n].background = makeShapeBg(if (active) cAccent else cCard, if (active) cAccentStroke else cBtnStroke, false)
            navBtns[n].setTextColor(if (active) cAccentText else cSubtext)
        }
    }

    private fun setScanBusy(busy: Boolean) {
        scanInProgress = busy
        pulseAnim?.cancel()
        pulseAnim = null
        scanIndicatorView.alpha = 1f
        scanIndicatorView.visibility = if (busy) View.VISIBLE else View.GONE
        if (busy) {
            pulseAnim = ObjectAnimator.ofFloat(scanIndicatorView, "alpha", 1f, 0.25f).apply {
                duration = 550L
                repeatMode = ObjectAnimator.REVERSE
                repeatCount = ObjectAnimator.INFINITE
                start()
            }
        }
    }

    private fun closeScanModal() { scanToken++; setScanBusy(false); scanModalOpen = false; scanBackdropView.visibility = View.GONE }

    private fun disconnectTv() {
        manualDisconnect = true; ready = false; connectedHost = null
        remote?.close(); remote = null
        uiState(StatusState.DISCONNECTED, cMuted); updateRemoteHeaderIndicator()
        if (scanModalOpen && scannedIps.isNotEmpty()) rebuildFoundTvCards()
    }

    private fun buildScanModal(prefs: android.content.SharedPreferences) {
        scanIconBadge = TextView(this).apply { text = "🖥"; setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(20f)); layoutParams = lp(LinearLayout.LayoutParams.WRAP_CONTENT, LinearLayout.LayoutParams.WRAP_CONTENT, 0f, 0, 0, 10, 0) }
        scanTitleView = TextView(this).apply { text = t("scanModalTitle"); typeface = Typeface.DEFAULT_BOLD; setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(18f)); layoutParams = lp(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f) }
        scanCloseBtn = Button(this).apply {
            text = "✕"; background = null; setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(18f)); typeface = Typeface.DEFAULT_BOLD; isAllCaps = false
            minWidth = 0; minimumWidth = 0; minHeight = 0; minimumHeight = 0; setPadding(px(8), px(4), px(8), px(4))
            layoutParams = lp(LinearLayout.LayoutParams.WRAP_CONTENT, LinearLayout.LayoutParams.WRAP_CONTENT)
            setOnClickListener { tap(v = this); closeScanModal() }
        }
        val header = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL
            layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT, 0f, 0, 0, 0, 14)
            addView(scanIconBadge); addView(scanTitleView); addView(scanCloseBtn)
        }
        scanMessageView = TextView(this).apply {
            text = t("scanSearching"); setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(14.5f)); setLineSpacing(px(3).toFloat(), 1.1f)
            layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT, 0f, 0, 0, 0, 14)
        }
        scanIndicatorView = View(this).apply {
            visibility = View.GONE
            background = GradientDrawable().apply { shape = GradientDrawable.OVAL; setColor(cAccentStroke) }
            layoutParams = LinearLayout.LayoutParams(px(18), px(18)).apply { gravity = Gravity.CENTER_HORIZONTAL; setMargins(0, px(4), 0, px(14)) }
        }
        scanResultsContainer = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL; visibility = View.GONE
            layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT, 0f, 0, 0, 0, 8); tag = prefs
        }
        scanTroublesTipView = TextView(this).apply {
            text = t("scanTroublesTip"); visibility = View.GONE; setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(12.5f)); setPadding(px(12), px(10), px(12), px(10))
            layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT, 0f, 0, 0, 0, 10)
        }
        scanTroublesBtn = TextView(this).apply {
            text = t("scanTroubles"); typeface = Typeface.DEFAULT_BOLD; isClickable = true; isFocusable = true
            setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(13.5f)); setPadding(px(4), px(6), px(4), px(2))
            layoutParams = lp(LinearLayout.LayoutParams.WRAP_CONTENT, LinearLayout.LayoutParams.WRAP_CONTENT)
            setOnClickListener { tap(v = this); scanTroublesVisible = !scanTroublesVisible; scanTroublesTipView.visibility = if (scanTroublesVisible) View.VISIBLE else View.GONE }
        }
        scanDialogCardView = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL; setPadding(px(20), px(20), px(20), px(20))
            layoutParams = FrameLayout.LayoutParams(FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.WRAP_CONTENT, Gravity.CENTER).apply { setMargins(px(24), px(24), px(24), px(24)) }
            addView(header); addView(scanMessageView); addView(scanIndicatorView)
            addView(scanResultsContainer); addView(scanTroublesTipView)
            addView(LinearLayout(this@MainActivity).apply {
                orientation = LinearLayout.HORIZONTAL; gravity = Gravity.END or Gravity.CENTER_VERTICAL
                layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT, 0f, 0, 6, 0, 0)
                addView(scanTroublesBtn)
            })
            isClickable = true; isFocusable = true
        }
        scanBackdropView = FrameLayout(this).apply {
            visibility = View.GONE; setBackgroundColor(Color.parseColor("#B3000000")); isClickable = true; isFocusable = true
            layoutParams = FrameLayout.LayoutParams(FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.MATCH_PARENT)
            setOnClickListener { closeScanModal() }; addView(scanDialogCardView)
        }
    }

    private fun styledEdit(hintText: String, textSizeSp: Float, padH: Int, padV: Int, params: LinearLayout.LayoutParams) = EditText(this).apply {
        hint = hintText; setHintTextColor(cMuted); setTextColor(cText); typeface = Typeface.DEFAULT_BOLD
        setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(textSizeSp)); setPadding(px(padH), px(padV), px(padH), px(padV)); setSingleLine(); layoutParams = params
    }

    private fun sectionTitle(textVal: String, sizeSp: Float, padB: Int) = TextView(this).apply {
        text = textVal; setTextColor(cText); typeface = Typeface.DEFAULT_BOLD
        setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(sizeSp)); setPadding(px(2), 0, 0, px(padB))
    }

    @SuppressLint("ClickableViewAccessibility")
    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        try {
            step = "1-prefs"
            dp = resources.displayMetrics.density.coerceAtLeast(0.75f)
            sp = resources.displayMetrics.scaledDensity.coerceAtLeast(0.75f)
            val prefs = getSharedPreferences("tv", MODE_PRIVATE)
            val paired = prefs.getBoolean("paired", false)
            hapticStrength = prefs.getInt("haptic_level", if (prefs.getBoolean("haptic", true)) 2 else 0).coerceIn(0, 3)
            wheelSizeMode = prefs.getInt("wheel_size", 1).coerceIn(0, wheelSizes.lastIndex)
            autoConnectEnabled = prefs.getBoolean("auto_connect", true)
            paletteIndex = prefs.getInt("palette", 0).coerceIn(0, palettes.lastIndex)
            currentLang = (prefs.getString("lang", "tr") ?: "tr").let { if (stringsMap.containsKey(it)) it else "tr" }
            lastStatusState = if (paired) StatusState.DISCONNECTED else StatusState.ENTER_IP
            lastStatusDotColor = cMuted

            step = "2-ipBox/codeBox"
            ipBox = styledEdit("192.168.1.105", 17f, 18, 15, lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT, 0f, 0, 0, 0, 12)).apply { setText(prefs.getString("ip", "")) }
            codeBox = styledEdit(t("codeHint"), 16f, 16, 14, lp(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f, 0, 0, 10, 0))
            confirmPairBtnView = Button(this).apply { text = t("confirm"); layoutParams = lp(LinearLayout.LayoutParams.WRAP_CONTENT, px(54)); setOnClickListener { tap(v = this); finishPairing(codeBox.text.toString()) } }
            codeRow = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL; visibility = View.GONE; setPadding(0, px(12), 0, 0); addView(codeBox); addView(confirmPairBtnView) }

            step = "3-status/power"
            statusDot = View(this).apply { layoutParams = lp(px(10), px(10), 0f, 0, 0, 10, 0); background = GradientDrawable().apply { shape = GradientDrawable.OVAL; setColor(cMuted) } }
            status = TextView(this).apply { text = formatStatus(lastStatusState, null); setTextColor(cSubtext); setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(13.5f)); setSingleLine() }

            powerBtnView = Button(this).apply { text = "⏻"; layoutParams = lp(px(48), px(48)); setOnClickListener { tap(v = this); sendKey(26) } }
            remoteHeaderDot = View(this).apply { layoutParams = lp(px(10), px(10), 0f, 10, 0, 8, 0); background = GradientDrawable().apply { shape = GradientDrawable.OVAL; setColor(cMuted) } }
            remoteHeaderTvName = TextView(this).apply { text = t("tvDeviceFallback"); typeface = Typeface.DEFAULT_BOLD; setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(15.5f)); setSingleLine(); layoutParams = lp(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f) }
            remoteHeaderSettingsBtn = Button(this).apply {
                text = "⚙"; layoutParams = lp(px(48), px(48))
                setOnClickListener { tap(v = this); settingsOpen = true; show(1); settingsSectionView.visibility = View.VISIBLE; styleBtn(openSettingsBtnView, cAccent, cAccentStroke, cAccentText, 15f, 18) }
            }

            val initialSize = wheelSizes[wheelSizeMode].second.second
            dpadWheelView = DpadWheelView(this) { zone ->
                tap(v = dpadWheelView)
                when (zone) { DpadZone.UP -> sendKey(19); DpadZone.RIGHT -> sendKey(22); DpadZone.DOWN -> sendKey(20); DpadZone.LEFT -> sendKey(21); DpadZone.CENTER -> sendKey(23); DpadZone.NONE -> Unit }
            }.apply { layoutParams = LinearLayout.LayoutParams(px(initialSize), px(initialSize)).apply { setMargins(0, px(6), 0, px(6)) } }

            val remoteHeaderRow = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL; layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, px(54), 0f, 0, 2, 0, 10); addView(powerBtnView); addView(remoteHeaderDot); addView(remoteHeaderTvName); addView(remoteHeaderSettingsBtn) }
            val volumeRow = LinearLayout(this).apply {
                orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER; layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, px(62), 0f, 0, 0, 0, 8)
                listOf("🔇" to 164, "🔉" to 25, "🔊" to 24, "★" to 176, "↺" to 82).forEachIndexed { idx, (lbl, code) ->
                    if (idx > 0) addView(View(this@MainActivity).apply { layoutParams = lp(px(14), px(1)) })
                    addView(roundActionKey(lbl, code))
                }
            }
            val bottomKeysRow = LinearLayout(this).apply {
                orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER; layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, px(72), 0f, 0, 8, 0, 4)
                addView(roundActionKey("←", 4, 68)); addView(View(this@MainActivity).apply { layoutParams = lp(px(36), px(1)) }); addView(roundActionKey("⌂", 3, 68))
            }
            step = "4-remote ekranı"
            screens.add(LinearLayout(this).apply {
                orientation = LinearLayout.VERTICAL; gravity = Gravity.CENTER_HORIZONTAL; visibility = View.GONE; setPadding(px(14), px(6), px(14), px(8))
                addView(remoteHeaderRow); addView(volumeRow); addView(dpadWheelView); addView(bottomKeysRow)
            })

            step = "5-connect ekranı"
            connectBtnView = Button(this).apply {
                text = t("connect"); layoutParams = lp(0, px(58), 1f, 0, 0, 6, 0)
                setOnClickListener { tap(v = this); manualDisconnect = false; prefs.edit().putString("ip", ipBox.text.toString().trim()).apply(); if (prefs.getBoolean("paired", false)) connectClicked() else startPairing() }
            }
            openSettingsBtnView = Button(this).apply {
                text = "⚙ ${t("settings")}"; layoutParams = lp(0, px(58), 1f, 6, 0, 0, 0)
                setOnClickListener { tap(v = this); settingsOpen = !settingsOpen; settingsSectionView.visibility = if (settingsOpen) View.VISIBLE else View.GONE; styleBtn(this, if (settingsOpen) cAccent else cBtn, if (settingsOpen) cAccentStroke else cBtnStroke, if (settingsOpen) cAccentText else cText, 15f, 18) }
            }
            scanTvBtnView = Button(this).apply { text = t("scanTv"); layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, px(50), 0f, 0, 10, 0, 0); setOnClickListener { tap(v = this); openAndScanNetwork(prefs) } }
            tvIpTitleView = sectionTitle(t("tvIp"), 18f, 10)
            connectCardView = LinearLayout(this).apply {
                orientation = LinearLayout.VERTICAL; setPadding(px(16), px(18), px(16), px(18)); layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT)
                addView(tvIpTitleView); addView(ipBox); addView(row(connectBtnView, openSettingsBtnView).apply { layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT) }); addView(scanTvBtnView); addView(codeRow)
            }

            step = "6-dropdownlar"
            fun makeDropdownContainer() = LinearLayout(this).apply {
                orientation = LinearLayout.VERTICAL; visibility = View.GONE
                layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT, 0f, 0, 4, 0, 4)
            }

            val (vh, vl, vv) = createDropdownHeader { vibDropdownOpen = !vibDropdownOpen; refreshDropdowns() }
            vibHeaderRow = vh; vibHeaderLabel = vl; vibHeaderValue = vv
            vibOptionsContainer = makeDropdownContainer().apply {
                for ((lvl, _) in vibLevels) {
                    val r = optionRow(t("vibOff"), null) { hapticStrength = lvl; prefs.edit().putInt("haptic_level", lvl).putBoolean("haptic", lvl > 0).apply(); vibDropdownOpen = false; tap(levelOverride = lvl, v = this); refreshDropdowns() }
                    vibRows.add(lvl to r); addView(r)
                }
            }

            val (sh, sl, sv) = createDropdownHeader { sizeDropdownOpen = !sizeDropdownOpen; refreshDropdowns() }
            sizeHeaderRow = sh; sizeHeaderLabel = sl; sizeHeaderValue = sv
            sizeOptionsContainer = makeDropdownContainer().apply {
                for ((mode, _) in wheelSizes) {
                    val r = optionRow(t("sizeMedium"), null) { wheelSizeMode = mode; prefs.edit().putInt("wheel_size", mode).apply(); sizeDropdownOpen = false; val p = px(wheelSizes[mode].second.second); dpadWheelView.layoutParams = LinearLayout.LayoutParams(p, p).apply { setMargins(0, px(6), 0, px(6)) }; refreshDropdowns() }
                    sizeRows.add(mode to r); addView(r)
                }
            }

            autoConnectBtn = Button(this).apply {
                text = t(if (autoConnectEnabled) "autoOn" else "autoOff"); layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, px(50), 0f, 0, 8, 0, 4)
                setOnClickListener { tap(v = this); autoConnectEnabled = !autoConnectEnabled; prefs.edit().putBoolean("auto_connect", autoConnectEnabled).apply(); text = t(if (autoConnectEnabled) "autoOn" else "autoOff"); styleBtn(this, if (autoConnectEnabled) cBtn else cCard, cBtnStroke, if (autoConnectEnabled) cText else cSubtext, 14f, 16) }
            }

            val (ph, pl, pv) = createDropdownHeader { paletteDropdownOpen = !paletteDropdownOpen; refreshDropdowns() }
            paletteHeaderRow = ph; paletteHeaderLabel = pl; paletteHeaderValue = pv
            paletteOptionsContainer = makeDropdownContainer().apply {
                for (idx in palettes.indices) {
                    val p = palettes[idx]
                    val r = optionRow(t(p.key), p.accent) { prefs.edit().putInt("palette", idx).apply(); paletteDropdownOpen = false; applyPalette(idx, switchTab = false) }
                    paletteRows.add(idx to r); addView(r)
                }
            }

            val (lh, ll, lv) = createDropdownHeader { langDropdownOpen = !langDropdownOpen; refreshDropdowns() }
            langHeaderRow = lh; langHeaderLabel = ll; langHeaderValue = lv
            langOptionsContainer = makeDropdownContainer().apply {
                for ((code, label) in languages) {
                    val r = optionRow(label, null) { prefs.edit().putString("lang", code).apply(); langDropdownOpen = false; applyLanguage(code) }
                    langRows.add(code to r); addView(r)
                }
            }

            resetPairBtnView = Button(this).apply {
                text = t("resetPair"); layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, px(50), 0f, 0, 12, 0, 0)
                setOnClickListener { tap(v = this); prefs.edit().putBoolean("paired", false).apply(); manualDisconnect = true; pairConn?.close(); pairConn = null; remote?.close(); remote = null; connectedHost = null; ready = false; codeRow.visibility = View.GONE; uiState(StatusState.PAIR_RESET, cMuted); updateRemoteHeaderIndicator() }
            }
            contactUsBtnView = Button(this).apply { text = t("contactUs"); layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, px(50), 0f, 0, 8, 0, 0); setOnClickListener { tap(v = this); openInstagram() } }
            step = "7-settings kartı"
            settingsTitleView = sectionTitle(t("settings"), 17.5f, 6)

            settingsCardView = LinearLayout(this).apply {
                orientation = LinearLayout.VERTICAL; setPadding(px(16), px(16), px(16), px(16))
                layoutParams = LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT)
                addView(settingsTitleView); addView(vibHeaderRow); addView(vibOptionsContainer); addView(sizeHeaderRow); addView(sizeOptionsContainer)
                addView(autoConnectBtn); addView(paletteHeaderRow); addView(paletteOptionsContainer); addView(langHeaderRow); addView(langOptionsContainer)
                addView(resetPairBtnView); addView(contactUsBtnView)
            }
            settingsSectionView = LinearLayout(this).apply {
                orientation = LinearLayout.VERTICAL; visibility = View.GONE
                layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT, 0f, 0, 12, 0, 0)
                addView(settingsCardView)
            }
            screens.add(ScrollView(this).apply {
                visibility = View.GONE
                addView(LinearLayout(this@MainActivity).apply {
                    orientation = LinearLayout.VERTICAL; gravity = Gravity.CENTER_HORIZONTAL; setPadding(px(14), px(10), px(14), px(12))
                    addView(connectCardView); addView(settingsSectionView)
                })
            })

            step = "8-rootView"
            topBarView = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL; setPadding(px(16), px(11), px(16), px(11)); layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT, 0f, 14, 2, 14, 6); addView(statusDot); addView(status) }
            val content = FrameLayout(this).apply { layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, 0, 1f); for (sc in screens) addView(sc, FrameLayout.LayoutParams(FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.MATCH_PARENT)) }
            val bottomNav = row(nav(t("tabRemote"), 0), nav(t("tabConnect"), 1)).apply { setPadding(px(8), px(2), px(8), px(4)) }
            rootView = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL; setPadding(px(4), px(26), px(4), px(6)); addView(topBarView); addView(content); addView(bottomNav) }

            step = "9-scan modal"
            buildScanModal(prefs)
            val shell = FrameLayout(this)
            shell.addView(this@MainActivity.rootView, FrameLayout.LayoutParams(FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.MATCH_PARENT))
            shell.addView(scanBackdropView, FrameLayout.LayoutParams(FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.MATCH_PARENT))

            step = "10-ağaç kontrolü"
            findCycle(shell)?.let { throw IllegalStateException(it) }
            step = "11-setContentView"
            setContentView(shell)
            step = "12-applyPalette"

            currentScreen = if (paired && ipBox.text.isNotBlank()) 0 else 1
            applyPalette(paletteIndex, switchTab = true)
            step = "13-connectClicked"
            if (currentScreen == 0 && autoConnectEnabled) connectClicked()
        } catch (e: Throwable) {
            setContentView(TextView(this).apply {
                text = "Açılış hatası [adım: $step]\n${e.javaClass.simpleName}: ${e.message}"
                setTextColor(Color.WHITE); setBackgroundColor(Color.BLACK); setPadding(36, 64, 36, 36); textSize = 12f
            })
        }
    }

    @Deprecated("Deprecated in Java")
    override fun onBackPressed() {
        if (scanModalOpen) { closeScanModal(); return }
        @Suppress("DEPRECATION") super.onBackPressed()
    }

    private fun openInstagram() {
        try { startActivity(Intent(Intent.ACTION_VIEW, Uri.parse(instagramUrl)).apply { setPackage("com.instagram.android") }) }
        catch (_: Exception) { try { startActivity(Intent(Intent.ACTION_VIEW, Uri.parse(instagramUrl))) } catch (_: Exception) {} }
    }

    private fun getLocalSubnetPrefix(): String? {
        return try {
            val cm = getSystemService(Context.CONNECTIVITY_SERVICE) as ConnectivityManager
            val net = cm.activeNetwork ?: return null
            cm.getLinkProperties(net)?.linkAddresses?.firstNotNullOfOrNull { linkAddr ->
                val addr = linkAddr.address
                if (addr is Inet4Address && !addr.isLoopbackAddress) addr.hostAddress?.split(".")?.takeIf { it.size == 4 }?.let { "${it[0]}.${it[1]}.${it[2]}" } else null
            }
        } catch (_: Exception) { null }
    }

    private fun buildFoundTvCard(prefs: android.content.SharedPreferences, ip: String): LinearLayout {
        val isDeviceConnected = (ready && remote != null && connectedHost == ip)
        return LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL; setPadding(px(14), px(12), px(14), px(12))
            layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT, 0f, 0, 0, 0, 10)
            background = makeCardBg(cSurface, if (isDeviceConnected) cGreen else cBtnStroke, 18)
            addView(TextView(this@MainActivity).apply { text = "🖥"; setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(20f)); setTextColor(cText); layoutParams = lp(LinearLayout.LayoutParams.WRAP_CONTENT, LinearLayout.LayoutParams.WRAP_CONTENT, 0f, 0, 0, 12, 0) })
            addView(LinearLayout(this@MainActivity).apply {
                orientation = LinearLayout.VERTICAL; layoutParams = lp(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f, 0, 0, 8, 0)
                addView(TextView(this@MainActivity).apply { text = t("tvDeviceFallback"); typeface = Typeface.DEFAULT_BOLD; setTextColor(cText); setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(14.5f)); setSingleLine() })
                addView(TextView(this@MainActivity).apply { text = ip; setTextColor(cSubtext); setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(12.5f)); setSingleLine(); layoutParams = lp(LinearLayout.LayoutParams.WRAP_CONTENT, LinearLayout.LayoutParams.WRAP_CONTENT, 0f, 0, 2, 0, 0) })
            })
            if (isDeviceConnected) {
                addView(Button(this@MainActivity).apply {
                    text = "✕ ${t("disconnect")}"; layoutParams = lp(LinearLayout.LayoutParams.WRAP_CONTENT, px(38))
                    styleBtn(this, cRedSolid, cRedStroke, Color.WHITE, 12.5f, 16); setPadding(px(12), 0, px(12), 0)
                    setOnClickListener { tap(v = this); disconnectTv() }
                })
            } else {
                isClickable = true; isFocusable = true; applyPressAnim(this)
                setOnClickListener {
                    tap(v = this); manualDisconnect = false; ipBox.setText(ip); prefs.edit().putString("ip", ip).apply(); closeScanModal()
                    if (prefs.getBoolean("paired", false)) connectClicked() else startPairing()
                }
            }
        }
    }

    private fun rebuildFoundTvCards() {
        val prefs = scanResultsContainer.tag as? android.content.SharedPreferences ?: return
        scanResultsContainer.removeAllViews()
        if (scannedIps.isEmpty()) { scanResultsContainer.visibility = View.GONE; return }
        for (ip in scannedIps) scanResultsContainer.addView(buildFoundTvCard(prefs, ip))
        scanResultsContainer.visibility = View.VISIBLE
    }

    private fun openAndScanNetwork(prefs: android.content.SharedPreferences) {
        val token = ++scanToken
        scanModalOpen = true; scanTroublesVisible = false; scanTroublesTipView.visibility = View.GONE
        scannedIps.clear(); scanResultsContainer.removeAllViews(); scanResultsContainer.visibility = View.GONE; scanBackdropView.visibility = View.VISIBLE

        val prefix = getLocalSubnetPrefix()
        if (prefix == null) {
            setScanBusy(false); scanMessageView.text = t(StatusState.SCAN_NO_WIFI.name)
            uiState(StatusState.SCAN_NO_WIFI, cRedStroke); return
        }

        setScanBusy(true); scanMessageView.text = t("scanSearching")
        uiState(StatusState.SCANNING, cAccentStroke)

        fastIo.execute {
            val found = Collections.synchronizedList(ArrayList<String>())
            val latch = CountDownLatch(254); val pool = Executors.newFixedThreadPool(24)
            for (lastOctet in 1..254) {
                if (token != scanToken) { latch.countDown(); continue }
                pool.execute {
                    try {
                        if (token == scanToken) {
                            val candidate = "$prefix.$lastOctet"
                            if ((isTvPortOpen(candidate, 6466, 220) || isTvPortOpen(candidate, 6467, 220)) && !found.contains(candidate)) {
                                found.add(candidate)
                                val sortedNow = found.distinct().sortedBy { it.substringAfterLast(".").toIntOrNull() ?: 999 }
                                runOnUiThread {
                                    if (token == scanToken && scanModalOpen) { scannedIps.clear(); scannedIps.addAll(sortedNow); rebuildFoundTvCards() }
                                }
                            }
                        }
                    } finally { latch.countDown() }
                }
            }
            latch.await(5500, TimeUnit.MILLISECONDS); pool.shutdownNow()
            if (token != scanToken) return@execute

            val uniqueIps = found.distinct().sortedBy { it.substringAfterLast(".").toIntOrNull() ?: 999 }
            runOnUiThread {
                if (token != scanToken) return@runOnUiThread
                scannedIps.clear(); scannedIps.addAll(uniqueIps); rebuildFoundTvCards()
                setScanBusy(false)
                if (uniqueIps.isEmpty()) { scanMessageView.text = t(StatusState.SCAN_NONE.name); uiState(StatusState.SCAN_NONE, cRedStroke) }
                else { scanMessageView.text = "${t(StatusState.SCAN_FOUND.name)} (${uniqueIps.size})"; uiState(StatusState.SCAN_FOUND, cGreen, uniqueIps.first()) }
            }
        }
    }

    private fun isTvPortOpen(ip: String, port: Int, timeoutMs: Int): Boolean = try {
        Socket().use { it.connect(InetSocketAddress(ip, port), timeoutMs); true }
    } catch (_: Exception) { false }

    private fun nav(label: String, i: Int) = Button(this).apply {
        text = label; typeface = Typeface.DEFAULT_BOLD; isAllCaps = false; setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(14.5f))
        setPadding(px(6), px(2), px(6), px(2)); layoutParams = lp(0, px(56), 1f, 5, 2, 5, 4)
        navBtns.add(this); applyPressAnim(this); setOnClickListener { tap(v = this); show(i) }
    }

    private fun row(vararg views: View) = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER; for (v in views) addView(v) }

    private fun roundActionKey(label: String, code: Int, sizeDp: Int = 52) = Button(this).apply {
        text = label; layoutParams = lp(px(sizeDp), px(sizeDp)); roundActionBtns.add(this); setOnClickListener { tap(v = this); sendKey(code) }
    }

    private fun uiState(state: StatusState, dotColor: Int, detail: String? = null) = runOnUiThread {
        lastStatusState = state; lastStatusDetail = detail; lastStatusDotColor = dotColor
        status.text = formatStatus(state, detail)
        (statusDot.background as? GradientDrawable)?.setColor(dotColor)
        updateRemoteHeaderIndicator()
    }

    private fun identity(): Identity {
        identity?.let { return it }
        val kf = File(filesDir, "client.key"); val cf = File(filesDir, "client.crt")
        val id = if (kf.exists() && cf.exists()) {
            Identity(KeyFactory.getInstance("RSA").generatePrivate(PKCS8EncodedKeySpec(kf.readBytes())), CertificateFactory.getInstance("X.509").generateCertificate(cf.inputStream()) as X509Certificate)
        } else {
            val kp = KeyPairGenerator.getInstance("RSA").apply { initialize(2048) }.generateKeyPair()
            val name = X500Name("CN=atvremote"); val now = Date()
            val cert = JcaX509CertificateConverter().getCertificate(JcaX509v3CertificateBuilder(name, BigInteger.valueOf(System.currentTimeMillis()), now, Date(now.time + 20L * 365L * 24L * 3600L * 1000L), name, kp.public).build(JcaContentSignerBuilder("SHA256withRSA").build(kp.private)))
            kf.writeBytes(kp.private.encoded); cf.writeBytes(cert.encoded); Identity(kp.private, cert)
        }
        identity = id; return id
    }

    private fun openTls(h: String, port: Int, id: Identity, readTimeoutMs: Int): Conn {
        val ctx = SSLContext.getInstance("TLS").apply { init(arrayOf<KeyManager>(FixedKm(id)), arrayOf<TrustManager>(TrustAll()), null) }
        val s = (ctx.socketFactory.createSocket() as SSLSocket).apply { connect(InetSocketAddress(h, port), 2000); tcpNoDelay = true; soTimeout = readTimeoutMs; startHandshake() }
        return Conn(s)
    }

    private fun outer(field: Int, inner: ByteArray) = Pb.int(1, 2) + Pb.int(2, 200) + Pb.bytes(field, inner)

    private fun expect(c: Conn, field: Int) {
        while (true) {
            val m = Pb.parse(c.read()); val st = m.firstOrNull { it.num == 2 }?.number
            if (st != null && st != 200L) throw IllegalStateException("TV eşleştirmeyi reddetti ($st)")
            if (m.any { it.num == field }) return
        }
    }

    private fun startPairing() {
        val h = ipBox.text.toString().trim()
        if (h.isEmpty()) { uiState(StatusState.ENTER_IP, cRedStroke); return }
        host = h; uiState(StatusState.PAIRING_START, cAccentStroke)
        fastIo.execute {
            try {
                pairConn?.close()
                val c = openTls(h, 6467, identity(), 10000)
                pairServerCert = c.sock.session.peerCertificates[0] as X509Certificate
                c.send(outer(10, Pb.str(1, "atvremote") + Pb.str(2, "TV Kumanda"))); expect(c, 11)
                c.send(outer(20, Pb.bytes(1, Pb.int(1, 3) + Pb.int(2, 6)) + Pb.int(3, 1))); expect(c, 20)
                c.send(outer(30, Pb.bytes(1, Pb.int(1, 3) + Pb.int(2, 6)) + Pb.int(2, 1))); expect(c, 31)
                pairConn = c; runOnUiThread { codeRow.visibility = View.VISIBLE }; uiState(StatusState.ENTER_CODE, cAccentStroke)
            } catch (e: Exception) { uiState(StatusState.PAIRING_FAILED, cRedStroke, e.message) }
        }
    }

    private fun finishPairing(raw: String) {
        val code = raw.trim().uppercase()
        if (code.length != 6) { uiState(StatusState.CODE_LENGTH, cRedStroke); return }
        fastIo.execute {
            try {
                val c = pairConn ?: throw IllegalStateException(t("connect")); val serverCert = pairServerCert ?: throw IllegalStateException("Cert")
                val id = identity(); val clientPub = id.cert.publicKey as RSAPublicKey; val serverPub = serverCert.publicKey as RSAPublicKey
                val secret = MessageDigest.getInstance("SHA-256").apply {
                    update(clientPub.modulus.unsigned()); update(clientPub.publicExponent.unsigned())
                    update(serverPub.modulus.unsigned()); update(serverPub.publicExponent.unsigned()); update(hexToBytes(code.substring(2)))
                }.digest()
                c.send(outer(40, Pb.bytes(1, secret))); expect(c, 41); c.close(); pairConn = null; manualDisconnect = false
                getSharedPreferences("tv", MODE_PRIVATE).edit().putBoolean("paired", true).apply()
                runOnUiThread { codeRow.visibility = View.GONE }; uiState(StatusState.PAIRED_CONNECTING, cAccentStroke)
                connectRemote(); runOnUiThread { show(0) }
            } catch (e: Exception) { uiState(StatusState.CODE_REJECTED, cRedStroke, e.message) }
        }
    }

    private fun connectClicked() {
        val h = ipBox.text.toString().trim()
        if (h.isEmpty()) { uiState(StatusState.ENTER_IP, cRedStroke); return }
        host = h; manualDisconnect = false; uiState(StatusState.CONNECTING, cAccentStroke)
        fastIo.execute { try { connectRemote(); runOnUiThread { show(0) } } catch (e: Exception) { uiState(StatusState.CONNECT_FAILED, cRedStroke, e.message) } }
    }

    @Synchronized
    private fun connectRemote() {
        ready = false; remote?.close()
        val c = openTls(host, 6466, identity(), 0); remote = c; connectedHost = host
        fastIo.execute { readerLoop(c) }; waitReady()
    }

    private fun waitReady() { var waited = 0; while (!ready && waited < 1200) { Thread.sleep(10); waited += 10 } }

    private fun configureReply(): ByteArray {
        val info = Pb.str(1, "model") + Pb.str(2, "vendor") + Pb.int(3, 1) + Pb.str(4, "1") + Pb.str(5, "androidtv-remote") + Pb.str(6, "1.0.0")
        return Pb.bytes(1, Pb.int(1, 622) + Pb.bytes(2, info))
    }

    private fun readerLoop(c: Conn) {
        try {
            while (true) {
                for (f in Pb.parse(c.read())) {
                    when (f.num) {
                        1 -> c.send(configureReply())
                        2 -> c.send(Pb.bytes(2, Pb.int(1, 622)))
                        8 -> c.send(Pb.bytes(9, Pb.int(1, (Pb.parse(f.data).firstOrNull { it.num == 1 }?.number ?: 0L).toInt())))
                        40 -> { ready = true; uiState(StatusState.CONNECTED, cGreen); if (scanModalOpen && scannedIps.isNotEmpty()) runOnUiThread { rebuildFoundTvCards() } }
                    }
                }
            }
        } catch (_: Exception) {
            if (remote === c) { remote = null; ready = false; connectedHost = null; if (!manualDisconnect) uiState(StatusState.LOST, cRedStroke) }
        }
    }

    private fun writeKey(code: Int) {
        val msg = Pb.bytes(10, Pb.int(1, code) + Pb.int(2, 3))
        val c = remote
        if (c != null) { try { c.send(msg); return } catch (_: Exception) { remote = null; ready = false } }
        if (host.isEmpty()) throw IllegalStateException(t(StatusState.ENTER_IP.name))
        if (!reconnecting) { reconnecting = true; try { connectRemote() } finally { reconnecting = false } } else waitReady()
        (remote ?: throw IllegalStateException(t(StatusState.CONNECT_FAILED.name))).send(msg)
    }

    private fun sendKey(code: Int) = fastIo.execute { try { writeKey(code) } catch (e: Exception) { uiState(StatusState.SEND_FAILED, cRedStroke, e.message) } }

    override fun onDestroy() { super.onDestroy(); pulseAnim?.cancel(); pulseAnim = null; scanToken++; pairConn?.close(); remote?.close(); fastIo.shutdownNow() }
}
