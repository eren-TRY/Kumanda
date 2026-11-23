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
import android.net.Network
import android.net.NetworkCapabilities
import android.net.Uri
import android.net.wifi.WifiManager
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
import java.net.ConnectException
import java.net.Inet4Address
import java.net.InetSocketAddress
import java.net.NetworkInterface
import java.net.NoRouteToHostException
import java.net.Socket
import java.net.SocketTimeoutException
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
    override fun chooseServerAlias(k: Array<String>?, i: Array<Principal>?, s: Socket?): String? = null
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
private enum class IconKind { POWER, MUTE, VOL_DOWN, VOL_UP, BACK, HOME, IOS_SETTINGS, RECONNECT }

private class DpadWheelView(context: Context, private val onZoneTap: (DpadZone) -> Unit) : View(context) {
    private var sliceFill = Color.parseColor("#1D222E")
    private var sliceStroke = Color.parseColor("#2B3242")
    private var pressedSliceFill = Color.parseColor("#2D3648")
    private var centerFill = Color.parseColor("#E2E8F0")
    private var centerStroke = Color.parseColor("#94A3B8")
    private var arrowColor = Color.parseColor("#F8FAFC")
    private var activeZone = DpadZone.NONE
    private val outerRect = RectF()
    private val innerRect = RectF()
    private val slicePaths = Array(4) { Path() }
    private val chevronPath = Path()
    private val fillPaint = Paint(Paint.ANTI_ALIAS_FLAG).apply { style = Paint.Style.FILL }
    private val strokePaint = Paint(Paint.ANTI_ALIAS_FLAG).apply { style = Paint.Style.STROKE }
    private val arrowPaint = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        style = Paint.Style.STROKE
        strokeCap = Paint.Cap.ROUND
        strokeJoin = Paint.Join.ROUND
    }

    fun applyColors(sliceFill: Int, sliceStroke: Int, centerFill: Int, centerStroke: Int, @Suppress("UNUSED_PARAMETER") centerTextColor: Int, arrowColor: Int) {
        this.sliceFill = sliceFill; this.sliceStroke = sliceStroke
        this.pressedSliceFill = lighten(sliceFill, 1.24f)
        this.centerFill = centerFill; this.centerStroke = centerStroke
        this.arrowColor = arrowColor
        invalidate()
    }

    private fun lighten(color: Int, factor: Float): Int = Color.rgb(
        (Color.red(color) * factor).toInt().coerceIn(0, 255),
        (Color.green(color) * factor).toInt().coerceIn(0, 255),
        (Color.blue(color) * factor).toInt().coerceIn(0, 255)
    )

    override fun onMeasure(widthMeasureSpec: Int, heightMeasureSpec: Int) {
        val w = MeasureSpec.getSize(widthMeasureSpec); val h = MeasureSpec.getSize(heightMeasureSpec)
        val side = when { w > 0 && h > 0 -> min(w, h); w > 0 -> w; h > 0 -> h; else -> (326 * resources.displayMetrics.density).toInt() }
        val exact = MeasureSpec.makeMeasureSpec(side, MeasureSpec.EXACTLY)
        setMeasuredDimension(exact, exact)
    }

    override fun onSizeChanged(w: Int, h: Int, oldw: Int, oldh: Int) {
        super.onSizeChanged(w, h, oldw, oldh)
        if (w <= 0 || h <= 0) return
        val cx = w / 2f; val cy = h / 2f; val outerR = min(cx, cy) - 4f; val innerR = outerR * 0.29f
        outerRect.set(cx - outerR, cy - outerR, cx + outerR, cy + outerR)
        innerRect.set(cx - innerR, cy - innerR, cx + innerR, cy + innerR)
        val starts = floatArrayOf(-45f, 45f, 135f, 225f)
        for (i in 0 until 4) {
            slicePaths[i].apply { reset(); arcTo(outerRect, starts[i], 90f, true); arcTo(innerRect, starts[i] + 90f, -90f, false); close() }
        }
    }

    private fun zoneAt(x: Float, y: Float): DpadZone {
        val cx = width / 2f; val cy = height / 2f; val outerR = min(cx, cy) - 4f; val innerR = outerR * 0.29f
        val dist = hypot((x - cx).toDouble(), (y - cy).toDouble())
        if (dist > outerR) return DpadZone.NONE
        if (dist <= innerR) return DpadZone.CENTER
        var deg = Math.toDegrees(atan2((y - cy).toDouble(), (x - cx).toDouble())).toFloat()
        if (deg < 0f) deg += 360f
        return when { deg >= 315f || deg < 45f -> DpadZone.RIGHT; deg < 135f -> DpadZone.DOWN; deg < 225f -> DpadZone.LEFT; else -> DpadZone.UP }
    }

    private fun drawChevron(canvas: Canvas, cx: Float, cy: Float, arm: Float, deg: Double) {
        canvas.save()
        canvas.translate(cx, cy)
        canvas.rotate(deg.toFloat())
        chevronPath.reset()
        chevronPath.moveTo(-arm * 0.48f, arm * 0.22f)
        chevronPath.lineTo(0f, -arm * 0.24f)
        chevronPath.lineTo(arm * 0.48f, arm * 0.22f)
        canvas.drawPath(chevronPath, arrowPaint)
        canvas.restore()
    }

    override fun onDraw(canvas: Canvas) {
        super.onDraw(canvas)
        if (width <= 0 || height <= 0) return
        val cx = width / 2f; val cy = height / 2f; val outerR = min(cx, cy) - 4f; val innerR = outerR * 0.29f
        strokePaint.strokeWidth = maxOf(2f, outerR * 0.014f); strokePaint.color = sliceStroke
        val zones = arrayOf(DpadZone.RIGHT, DpadZone.DOWN, DpadZone.LEFT, DpadZone.UP)
        for (i in 0 until 4) {
            fillPaint.color = if (activeZone == zones[i]) pressedSliceFill else sliceFill
            canvas.drawPath(slicePaths[i], fillPaint); canvas.drawPath(slicePaths[i], strokePaint)
        }
        val midR = (outerR + innerR) * 0.54f
        arrowPaint.color = arrowColor
        arrowPaint.strokeWidth = maxOf(3f, outerR * 0.025f)
        val arm = outerR * 0.135f
        for (deg in listOf(0.0, 90.0, 180.0, 270.0)) {
            val rad = Math.toRadians(deg - 90.0)
            drawChevron(canvas, cx + (midR * cos(rad)).toFloat(), cy + (midR * sin(rad)).toFloat(), arm, deg)
        }
        fillPaint.color = if (activeZone == DpadZone.CENTER) lighten(centerFill, 0.9f) else centerFill
        strokePaint.color = centerStroke
        canvas.drawCircle(cx, cy, innerR, fillPaint); canvas.drawCircle(cx, cy, innerR, strokePaint)
    }

    private fun resetScale() { animate().cancel(); scaleX = 1f; scaleY = 1f }
    private fun animateTap() { animate().cancel(); scaleX = 0.96f; scaleY = 0.96f; animate().scaleX(1f).scaleY(1f).setDuration(85L).start() }

    @SuppressLint("ClickableViewAccessibility")
    override fun onTouchEvent(event: MotionEvent): Boolean {
        when (event.actionMasked) {
            MotionEvent.ACTION_DOWN, MotionEvent.ACTION_MOVE -> {
                val z = zoneAt(event.x, event.y)
                if (z != activeZone) {
                    activeZone = z
                    if (z == DpadZone.NONE) {
                        resetScale()
                    } else if (event.actionMasked == MotionEvent.ACTION_DOWN) {
                        scaleX = 0.96f; scaleY = 0.96f
                    }
                    invalidate()
                }
                return true
            }
            MotionEvent.ACTION_UP -> {
                val z = zoneAt(event.x, event.y)
                if (z != DpadZone.NONE) { animateTap(); onZoneTap(z) } else { resetScale() }
                activeZone = DpadZone.NONE; invalidate(); performClick(); return true
            }
            MotionEvent.ACTION_CANCEL -> { resetScale(); activeZone = DpadZone.NONE; invalidate(); return true }
        }
        return super.onTouchEvent(event)
    }
    override fun performClick(): Boolean = super.performClick()
}

private class RemoteIconButton(
    context: Context,
    private val kind: IconKind
) : View(context) {
    private var iconColor = Color.parseColor("#F8FAFC")
    private var gearHoleColor = Color.parseColor("#141821")
    private val strokePaint = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        style = Paint.Style.STROKE
        strokeCap = Paint.Cap.ROUND
        strokeJoin = Paint.Join.ROUND
    }
    private val fillPaint = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        style = Paint.Style.FILL
    }
    private val rect = RectF()
    private val speakerPath = Path()
    private val gearPath = Path()

    fun setIconColor(color: Int) {
        iconColor = color
        invalidate()
    }

    fun setGearHoleColor(color: Int) {
        gearHoleColor = color
        invalidate()
    }

    private fun drawSpeakerBody(canvas: Canvas, cx: Float, cy: Float, u: Float) {
        speakerPath.reset()
        speakerPath.moveTo(cx - u * 0.68f, cy - u * 0.22f)
        speakerPath.lineTo(cx - u * 0.32f, cy - u * 0.22f)
        speakerPath.lineTo(cx + u * 0.14f, cy - u * 0.62f)
        speakerPath.lineTo(cx + u * 0.14f, cy + u * 0.62f)
        speakerPath.lineTo(cx - u * 0.32f, cy + u * 0.22f)
        speakerPath.lineTo(cx - u * 0.68f, cy + u * 0.22f)
        speakerPath.close()
        canvas.drawPath(speakerPath, fillPaint)
    }

    private fun drawIosGear(canvas: Canvas, cx: Float, cy: Float, u: Float) {
        val teeth = 12
        val rTip = u * 0.90f
        val rRoot = u * 0.70f
        val rInner = u * 0.28f
        gearPath.reset()
        val stepAngle = (2.0 * PI) / teeth
        for (i in 0 until teeth) {
            val base = i * stepAngle
            val a0 = base
            val a1 = base + stepAngle * 0.22
            val a2 = base + stepAngle * 0.34
            val a3 = base + stepAngle * 0.66
            val a4 = base + stepAngle * 0.78

            val x0 = cx + (rRoot * cos(a0)).toFloat()
            val y0 = cy + (rRoot * sin(a0)).toFloat()
            if (i == 0) gearPath.moveTo(x0, y0) else gearPath.lineTo(x0, y0)

            gearPath.lineTo(cx + (rRoot * cos(a1)).toFloat(), cy + (rRoot * sin(a1)).toFloat())
            gearPath.lineTo(cx + (rTip * cos(a2)).toFloat(), cy + (rTip * sin(a2)).toFloat())
            gearPath.lineTo(cx + (rTip * cos(a3)).toFloat(), cy + (rTip * sin(a3)).toFloat())
            gearPath.lineTo(cx + (rRoot * cos(a4)).toFloat(), cy + (rRoot * sin(a4)).toFloat())
        }
        gearPath.close()
        canvas.drawPath(gearPath, fillPaint)

        fillPaint.color = gearHoleColor
        canvas.drawCircle(cx, cy, rInner, fillPaint)
        strokePaint.color = iconColor
        strokePaint.strokeWidth = maxOf(2f, u * 0.14f)
        canvas.drawCircle(cx, cy, rInner, strokePaint)
        fillPaint.color = iconColor
    }

    override fun onDraw(canvas: Canvas) {
        super.onDraw(canvas)
        if (width <= 0 || height <= 0) return
        val w = width.toFloat(); val h = height.toFloat()
        val cx = w / 2f; val cy = h / 2f
        val s = min(w, h)
        val u = s * 0.26f
        strokePaint.color = iconColor
        fillPaint.color = iconColor
        strokePaint.strokeWidth = maxOf(2.4f, s * 0.052f)

        when (kind) {
            IconKind.POWER -> {
                val r = s * 0.25f
                rect.set(cx - r, cy - r + r * 0.14f, cx + r, cy + r + r * 0.14f)
                canvas.drawArc(rect, -58f, 296f, false, strokePaint)
                canvas.drawLine(cx, cy - r * 0.35f, cx, cy + r * 0.12f, strokePaint)
            }
            IconKind.MUTE -> {
                drawSpeakerBody(canvas, cx - u * 0.14f, cy, u)
                val x1 = cx + u * 0.34f; val x2 = cx + u * 0.80f
                val d = u * 0.24f
                canvas.drawLine(x1, cy - d, x2, cy + d, strokePaint)
                canvas.drawLine(x1, cy + d, x2, cy - d, strokePaint)
            }
            IconKind.VOL_DOWN -> {
                drawSpeakerBody(canvas, cx - u * 0.14f, cy, u)
                rect.set(cx + u * 0.12f, cy - u * 0.32f, cx + u * 0.60f, cy + u * 0.32f)
                canvas.drawArc(rect, -42f, 84f, false, strokePaint)
            }
            IconKind.VOL_UP -> {
                drawSpeakerBody(canvas, cx - u * 0.20f, cy, u)
                rect.set(cx + u * 0.06f, cy - u * 0.32f, cx + u * 0.50f, cy + u * 0.32f)
                canvas.drawArc(rect, -42f, 84f, false, strokePaint)
                rect.set(cx - u * 0.02f, cy - u * 0.54f, cx + u * 0.80f, cy + u * 0.54f)
                canvas.drawArc(rect, -42f, 84f, false, strokePaint)
            }
            IconKind.BACK -> {
                val a = u * 0.95f
                canvas.drawLine(cx - a * 0.80f, cy, cx + a * 0.80f, cy, strokePaint)
                canvas.drawLine(cx - a * 0.80f, cy, cx - a * 0.15f, cy - a * 0.68f, strokePaint)
                canvas.drawLine(cx - a * 0.80f, cy, cx - a * 0.15f, cy + a * 0.68f, strokePaint)
            }
            IconKind.HOME -> {
                val a = u * 0.92f
                val roofPath = Path().apply {
                    moveTo(cx, cy - a * 0.88f)
                    lineTo(cx - a * 0.88f, cy - a * 0.05f)
                    lineTo(cx - a * 0.58f, cy - a * 0.05f)
                    lineTo(cx - a * 0.58f, cy + a * 0.78f)
                    lineTo(cx - a * 0.20f, cy + a * 0.78f)
                    lineTo(cx - a * 0.20f, cy + a * 0.24f)
                    lineTo(cx + a * 0.20f, cy + a * 0.24f)
                    lineTo(cx + a * 0.20f, cy + a * 0.78f)
                    lineTo(cx + a * 0.58f, cy + a * 0.78f)
                    lineTo(cx + a * 0.58f, cy - a * 0.05f)
                    lineTo(cx + a * 0.88f, cy - a * 0.05f)
                    close()
                }
                canvas.drawPath(roofPath, fillPaint)
            }
            IconKind.IOS_SETTINGS -> {
                drawIosGear(canvas, cx, cy, u * 1.02f)
            }
            IconKind.RECONNECT -> {
                val r = u * 0.68f
                rect.set(cx - r, cy - r, cx + r, cy + r)
                canvas.drawArc(rect, -40f, 275f, false, strokePaint)
                canvas.drawLine(cx + r * 0.75f, cy - r * 0.65f, cx + r * 1.05f, cy - r * 0.15f, strokePaint)
                canvas.drawLine(cx + r * 0.75f, cy - r * 0.65f, cx + r * 0.25f, cy - r * 0.55f, strokePaint)
            }
        }
    }

    @SuppressLint("ClickableViewAccessibility")
    override fun onTouchEvent(event: MotionEvent): Boolean {
        when (event.actionMasked) {
            MotionEvent.ACTION_DOWN -> { animate().cancel(); scaleX = 0.93f; scaleY = 0.93f; return true }
            MotionEvent.ACTION_UP -> {
                animate().scaleX(1f).scaleY(1f).setDuration(85L).start()
                performClick()
                return true
            }
            MotionEvent.ACTION_CANCEL -> { animate().scaleX(1f).scaleY(1f).setDuration(85L).start(); return true }
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

private data class ReleaseNote(val version: String, val changes: List<String>)

private val releaseNotesMap = mapOf(
    "tr" to listOf(
        ReleaseNote(
            "v1.8",
            listOf(
                "Wi-Fi ağına doğrudan soket bağlama (bindSocket) eklenerek mobil veri/VPN çakışması giderildi.",
                "Zaman aşımı, bağlantı reddi ve ağ erişilemezlik hataları ayrıştırıldı."
            )
        ),
        ReleaseNote(
            "v1.7",
            listOf(
                "Bağlantı koptuğunda otomatik yeniden bağlanma ve soket temizleme akışı iyileştirildi.",
                "Hata mesajlarının daha net okunabilmesi için durum satırı genişletildi."
            )
        ),
        ReleaseNote(
            "v1.6",
            listOf(
                "Eşleştirme ve kumanda oturumu kararlılığı, zaman aşımı temizliği ve hata yönetimi iyileştirildi.",
                "Ağ taraması iptal/yenileme akışı ve açılış kurtarma ekranı geliştirildi."
            )
        ),
        ReleaseNote(
            "v1.5",
            listOf(
                "iPhone tarzı ayarlar dişlisi sadece Bağlantı ekranının sol altına eklendi.",
                "Bize Ulaşın butonuna basıldığında açılan iletişim penceresi ve Instagram seçeneği eklendi."
            )
        )
    ),
    "en" to listOf(
        ReleaseNote(
            "v1.8",
            listOf(
                "Bound sockets directly to the active Wi-Fi network to fix mobile data/VPN routing timeouts.",
                "Added clear error diagnostics for timeout, connection refused, and unreachable host."
            )
        ),
        ReleaseNote(
            "v1.7",
            listOf(
                "Improved automatic reconnection on connection loss and socket cleanup flow.",
                "Expanded status line for clearer error readability."
            )
        ),
        ReleaseNote(
            "v1.6",
            listOf(
                "Improved pairing and remote session stability, timeout cleanup, and error handling.",
                "Enhanced network scan cancellation/refresh flow and startup recovery screen."
            )
        ),
        ReleaseNote(
            "v1.5",
            listOf(
                "Added iPhone-style gear on Connection screen only, Contact Us sheet with Instagram, and socket/error improvements."
            )
        )
    )
)

private val stringsMap = mapOf(
    "tr" to mapOf(
        "tabRemote" to "Kumanda", "tabConnect" to "Bağlantı",
        "power" to "Güç", "tvIp" to "TV IP Adresi", "scanTv" to "Ağda TV Ara", "settings" to "Ayarlar",
        "updates" to "Güncellemeler", "updatesTitle" to "Sürüm Geçmişi ve Yenilikler", "back" to "Geri",
        "hapticLevel" to "Titreşim Şiddeti", "wheelSize" to "Orta Tuş Boyutu",
        "theme" to "Renk Paleti", "lang" to "Dil",
        "codeHint" to "6 haneli kod", "confirm" to "Onayla", "connect" to "Bağlan",
        "autoOn" to "Oto Bağlan: Açık", "autoOff" to "Oto Bağlan: Kapalı",
        "resetPair" to "Eşleştirmeyi Sıfırla", "contactUs" to "Bize Ulaşın",
        "contactOptionsTitle" to "İletişim Seçenekleri", "openInstagram" to "Instagram", "close" to "Kapat",
        "linkOpenFailed" to "Bağlantı açılamadı", "retry" to "Tekrar Dene",
        "vibOff" to "Kapalı", "vibLight" to "Hafif", "vibMed" to "Orta", "vibStrong" to "Güçlü",
        "sizeSmall" to "Küçük", "sizeMedium" to "Orta", "sizeLarge" to "Büyük",
        "palBlue" to "Mavi", "palEmerald" to "Zümrüt", "palPurple" to "Mor",
        "palAmber" to "Kehribar", "palBw" to "Siyah Beyaz", "palCrimson" to "Yakut",
        "palCyan" to "Camgöbeği", "palCoral" to "Mercan",
        "scanModalTitle" to "TV Cihazları", "scanSearching" to "Ağınızda TV cihazları aranıyor…",
        "scanTroubles" to "Bağlantı sorunları?",
        "scanTroublesTip" to "Telefon ve TV aynı Wi-Fi ağında olmalı ve cihaz izolasyonu kapalı olmalıdır. Bulunamazsa IP'yi elle girin.",
        "disconnect" to "Bağlantıyı Kes", "tvDeviceFallback" to "Android TV",
        StatusState.DISCONNECTED.name to "Bağlı değil", StatusState.ENTER_IP.name to "Geçerli bir TV IP adresi yaz (ör. 192.168.0.42)",
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
        "tabRemote" to "Remote", "tabConnect" to "Connection",
        "power" to "Power", "tvIp" to "TV IP Address", "scanTv" to "Find TV on Network", "settings" to "Settings",
        "updates" to "Updates", "updatesTitle" to "Version History & Changes", "back" to "Back",
        "hapticLevel" to "Haptic Strength", "wheelSize" to "Center Wheel Size",
        "theme" to "Color Palette", "lang" to "Language",
        "codeHint" to "6-digit code", "confirm" to "Confirm", "connect" to "Connect",
        "autoOn" to "Auto Connect: On", "autoOff" to "Auto Connect: Off",
        "resetPair" to "Reset Pairing", "contactUs" to "Contact Us",
        "contactOptionsTitle" to "Contact Options", "openInstagram" to "Instagram", "close" to "Close",
        "linkOpenFailed" to "Could not open link", "retry" to "Retry",
        "vibOff" to "Off", "vibLight" to "Light", "vibMed" to "Medium", "vibStrong" to "Strong",
        "sizeSmall" to "Small", "sizeMedium" to "Medium", "sizeLarge" to "Large",
        "palBlue" to "Blue", "palEmerald" to "Emerald", "palPurple" to "Purple",
        "palAmber" to "Amber", "palBw" to "Black & White", "palCrimson" to "Crimson",
        "palCyan" to "Cyan", "palCoral" to "Coral",
        "scanModalTitle" to "TV Devices", "scanSearching" to "Searching for TV devices on your network…",
        "scanTroubles" to "Connection troubles?",
        "scanTroublesTip" to "Keep phone and TV on the same Wi-Fi without AP isolation, or enter the TV IP manually.",
        "disconnect" to "Disconnect", "tvDeviceFallback" to "Android TV",
        StatusState.DISCONNECTED.name to "Disconnected", StatusState.ENTER_IP.name to "Enter a valid TV IPv4 address (e.g. 192.168.0.42)",
        StatusState.PAIRING_START.name to "Starting pairing…", StatusState.ENTER_CODE.name to "Enter the 6-digit code on TV and tap Confirm",
        StatusState.PAIRING_FAILED.name to "Pairing failed", StatusState.CODE_LENGTH.name to "Code must be 6 characters",
        StatusState.CODE_REJECTED.name to "Code rejected", StatusState.PAIRED_CONNECTING.name to "Paired — Connecting…",
        StatusState.CONNECTING.name to "Connecting…", StatusState.CONNECT_FAILED.name to "Connection failed",
        StatusState.CONNECTED.name to "Connected", StatusState.LOST.name to "Connection lost",
        StatusState.PAIR_RESET.name to "Pairing reset", StatusState.SEND_FAILED.name to "Failed to send",
        StatusState.SCANNING.name to "Scanning network for TV…", StatusState.SCAN_NO_WIFI.name to "Local Wi-Fi network not found",
        StatusState.SCAN_FOUND.name to "TV found", StatusState.SCAN_NONE.name to "No TV found on network"
    )
)

class MainActivity : Activity() {
    private val fastIo = Executors.newCachedThreadPool()
    private val pairLock = Any()
    private val connectLock = Any()
    private var identity: Identity? = null
    @Volatile private var remote: Conn? = null
    @Volatile private var ready = false
    @Volatile private var manualDisconnect = false
    @Volatile private var isActivityActive = true
    @Volatile private var scanToken = 0
    @Volatile private var pairConn: Conn? = null
    @Volatile private var pairServerCert: X509Certificate? = null
    @Volatile private var host = ""
    @Volatile private var connectedHost: String? = null
    @Volatile private var lastConnectAttemptMs = 0L
    @Volatile private var hapticStrength = 2
    @Volatile private var wheelSizeMode = 1
    @Volatile private var autoConnectEnabled = true
    private var currentLang = "tr"
    private var vibDropdownOpen = false
    private var sizeDropdownOpen = false
    private var paletteDropdownOpen = false
    private var langDropdownOpen = false
    private var scanModalOpen = false
    private var contactModalOpen = false
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
    private val wheelSizes = listOf(0 to ("sizeSmall" to 280), 1 to ("sizeMedium" to 326), 2 to ("sizeLarge" to 356))
    private val languages = listOf("tr" to "Türkçe", "en" to "English")

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
    private lateinit var powerBtnView: RemoteIconButton
    private lateinit var remoteHeaderTvName: TextView
    private lateinit var remoteHeaderDot: View
    private lateinit var bottomLeftGearBtn: RemoteIconButton
    private lateinit var connectCardView: LinearLayout
    private lateinit var settingsCardView: LinearLayout
    private lateinit var updatesCardView: LinearLayout
    private lateinit var updatesTitleView: TextView
    private lateinit var updatesListContainer: LinearLayout
    private lateinit var updatesBackBtnView: Button
    private lateinit var tvIpTitleView: TextView
    private lateinit var scanTvBtnView: Button
    private lateinit var settingsTitleView: TextView
    private lateinit var updatesBtnView: Button
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

    private lateinit var scanBackdropView: FrameLayout; private lateinit var scanDialogCardView: LinearLayout
    private lateinit var scanTitleView: TextView; private lateinit var scanCloseBtn: Button; private lateinit var scanIndicatorView: View
    private lateinit var scanMessageView: TextView; private lateinit var scanResultsContainer: LinearLayout
    private lateinit var scanTroublesBtn: TextView; private lateinit var scanTroublesTipView: TextView

    private lateinit var contactBackdropView: FrameLayout; private lateinit var contactDialogCardView: LinearLayout
    private lateinit var contactTitleView: TextView; private lateinit var contactIgBtn: Button; private lateinit var contactCloseBtn: Button

    private var dp = 1f; private var sp = 1f; private var currentScreen = 0
    private var step = "başlangıç"

    private val navBtns = ArrayList<Button>()
    private val roundIconBtns = ArrayList<RemoteIconButton>()
    private val vibRows = ArrayList<Pair<Int, LinearLayout>>(); private val sizeRows = ArrayList<Pair<Int, LinearLayout>>()
    private val paletteRows = ArrayList<Pair<Int, LinearLayout>>(); private val langRows = ArrayList<Pair<String, LinearLayout>>()
    private val screens = ArrayList<View>(); private val scannedIps = ArrayList<String>()

    private fun t(key: String): String =
        stringsMap[currentLang]?.get(key) ?: stringsMap.getValue("tr")[key] ?: key

    private fun px(v: Int) = (v * dp).toInt().coerceAtLeast(1)
    private fun scaledSp(v: Float) = v * (sp / dp).coerceIn(0.85f, 1.3f)
    private fun lp(w: Int, h: Int, weight: Float = 0f, l: Int = 0, top: Int = 0, r: Int = 0, b: Int = 0) =
        LinearLayout.LayoutParams(w, h, weight).apply { setMargins(px(l), px(top), px(r), px(b)) }

    private fun isValidIpv4(ip: String): Boolean {
        val parts = ip.split(".")
        if (parts.size != 4) return false
        return parts.all { p -> p.isNotEmpty() && p.all { it.isDigit() } && (p.toIntOrNull() in 0..255) }
    }

    private fun findWifiNetwork(): Network? {
        return try {
            val cm = getSystemService(Context.CONNECTIVITY_SERVICE) as ConnectivityManager
            cm.allNetworks.firstOrNull { net ->
                val caps = cm.getNetworkCapabilities(net)
                caps != null && caps.hasTransport(NetworkCapabilities.TRANSPORT_WIFI)
            } ?: cm.activeNetwork?.takeIf { net ->
                cm.getNetworkCapabilities(net)?.hasTransport(NetworkCapabilities.TRANSPORT_WIFI) == true
            }
        } catch (_: Exception) {
            null
        }
    }

    private fun bindSocketToWifi(socket: Socket) {
        try {
            findWifiNetwork()?.bindSocket(socket)
        } catch (_: Exception) {
        }
    }

    private fun diagnoseConnectionError(e: Exception, targetIp: String, port: Int): String {
        val wifiNet = findWifiNetwork()
        if (wifiNet == null) {
            return if (currentLang == "en") {
                "Phone is not connected to Wi-Fi. Turn on Wi-Fi on the same network as TV."
            } else {
                "Telefon Wi-Fi ağına bağlı değil. TV ile aynı Wi-Fi ağına bağlanın."
            }
        }
        return when (e) {
            is ConnectException -> {
                if (currentLang == "en") {
                    "TV ($targetIp:$port) refused connection. Android TV Remote Service may be off or unsupported on this TV."
                } else {
                    "TV ($targetIp:$port) bağlantıyı reddetti. TV'de Android TV Remote servisi kapalı veya bu TV desteklemiyor."
                }
            }
            is NoRouteToHostException -> {
                if (currentLang == "en") {
                    "No route to $targetIp. Check TV IP or router AP isolation."
                } else {
                    "$targetIp adresine ulaşılamıyor. TV IP'sini veya modem cihaz izolasyonunu kontrol edin."
                }
            }
            is SocketTimeoutException -> {
                if (currentLang == "en") {
                    "Timeout reaching $targetIp:$port. Verify TV is awake, IP is current, and port $port is open."
                } else {
                    "$targetIp:$port zaman aşımı. TV'nin açık olduğunu, IP'nin değişmediğini ve TV'nin Android TV/Google TV olduğunu kontrol edin."
                }
            }
            is SSLException -> {
                if (currentLang == "en") {
                    "TLS handshake failed (${e.message ?: "SSL"}). Try Reset Pairing in Settings."
                } else {
                    "TLS el sıkışması başarısız (${e.message ?: "SSL"}). Ayarlardan Eşleştirmeyi Sıfırla deneyin."
                }
            }
            else -> e.message ?: e.javaClass.simpleName
        }
    }

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
        (headerRow.tag as? TextView)?.apply { text = if (open) "^" else "v"; setTextColor(cSubtext) }
        container.visibility = if (open) View.VISIBLE else View.GONE
        for ((key, rowView) in rows) {
            val sel = isSelected(key); val st = rowStrokeFor(key)
            rowView.background = makeCardBg(if (sel) cCard else cBtn, if (sel) st else cBtnStroke, 16)
            labelFor(key)?.let { (rowView.getChildAt(textIdx) as? TextView)?.text = it }
            (rowView.getChildAt(textIdx) as? TextView)?.setTextColor(if (sel) cText else cSubtext)
            (rowView.getChildAt(markIdx) as? TextView)?.apply { text = if (sel) "*" else ""; setTextColor(st) }
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
        bottomLeftGearBtn.visibility = if (target == 1) View.VISIBLE else View.GONE
        if (target == 0) updateRemoteHeaderIndicator()
        val activeNavIndex: Int? = when (target) {
            0 -> 0
            1 -> 1
            else -> null
        }
        for (n in navBtns.indices) {
            val active = activeNavIndex != null && n == activeNavIndex
            navBtns[n].background = makeShapeBg(if (active) cAccent else cCard, if (active) cAccentStroke else cBtnStroke, false)
            navBtns[n].setTextColor(if (active) cAccentText else cSubtext)
        }
    }

    private fun rebuildReleaseNotes() {
        updatesListContainer.removeAllViews()
        val notes = releaseNotesMap[currentLang] ?: releaseNotesMap.getValue("tr")
        for (release in notes) {
            val card = LinearLayout(this).apply {
                orientation = LinearLayout.VERTICAL
                setPadding(px(14), px(12), px(14), px(12))
                background = makeCardBg(cCard, cBtnStroke, 18)
                layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT, 0f, 0, 0, 0, 10)
                addView(TextView(this@MainActivity).apply {
                    text = release.version
                    setTextColor(cAccentStroke)
                    typeface = Typeface.DEFAULT_BOLD
                    setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(15.5f))
                    layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT, 0f, 0, 0, 0, 6)
                })
                for (item in release.changes) {
                    addView(TextView(this@MainActivity).apply {
                        text = "- $item"
                        setTextColor(cText)
                        setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(13.5f))
                        setLineSpacing(px(2).toFloat(), 1.1f)
                        layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT, 0f, 0, 0, 0, 4)
                    })
                }
            }
            updatesListContainer.addView(card)
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
        if (navBtns.size >= 2) {
            navBtns[0].text = t("tabRemote")
            navBtns[1].text = t("tabConnect")
        }
        tvIpTitleView.text = t("tvIp")
        scanTvBtnView.text = t("scanTv")
        settingsTitleView.text = t("settings")
        updatesBtnView.text = t("updates")
        updatesTitleView.text = t("updatesTitle")
        updatesBackBtnView.text = t("back")
        codeBox.hint = t("codeHint")
        confirmPairBtnView.text = t("confirm")
        connectBtnView.text = t("connect")
        autoConnectBtn.text = t(if (autoConnectEnabled) "autoOn" else "autoOff")
        resetPairBtnView.text = t("resetPair")
        contactUsBtnView.text = t("contactUs")
        contactTitleView.text = t("contactOptionsTitle")
        contactIgBtn.text = t("openInstagram")
        contactCloseBtn.text = t("close")
        status.text = formatStatus(lastStatusState, lastStatusDetail)
        (statusDot.background as? GradientDrawable)?.setColor(lastStatusDotColor)
        updateRemoteHeaderIndicator()
        scanTitleView.text = t("scanModalTitle")
        scanTroublesBtn.text = t("scanTroubles")
        scanTroublesTipView.text = t("scanTroublesTip")
        if (scanInProgress) scanMessageView.text = t("scanSearching")
        if (scanModalOpen && scannedIps.isNotEmpty()) rebuildFoundTvCards()
        rebuildReleaseNotes()
        refreshDropdowns()
    }

    private fun applyLanguage(lang: String) {
        currentLang = if (stringsMap.containsKey(lang)) lang else "tr"
        applyTextsAndState()
    }

    private fun applyPalette(index: Int, switchTab: Boolean = false) {
        val p = palettes[index.coerceIn(0, palettes.lastIndex)]
        paletteIndex = index; cBg = p.bg; cCard = p.card; cSurface = p.surface; cBtn = p.btn; cBtnStroke = p.btnStroke
        cAccent = p.accent; cAccentStroke = p.accentStroke; cAccentText = p.accentText

        this@MainActivity.rootView.setBackgroundColor(cBg)
        topBarView.background = makeCardBg(cCard, cBtnStroke, 20)
        connectCardView.background = makeCardBg(cSurface, cBtnStroke, 28)
        settingsCardView.background = makeCardBg(cSurface, cBtnStroke, 28)
        updatesCardView.background = makeCardBg(cSurface, cBtnStroke, 28)
        updatesTitleView.setTextColor(cText)
        dpadWheelView.applyColors(cBtn, cBtnStroke, Color.parseColor("#E2E8F0"), Color.parseColor("#94A3B8"), Color.parseColor("#0F172A"), cText)
        ipBox.background = makeCardBg(cCard, cBtnStroke, 18); codeBox.background = makeCardBg(cCard, cBtnStroke, 18)

        remoteHeaderTvName.setTextColor(cText)
        powerBtnView.background = makeShapeBg(cRedSoft, cRedStroke, true)
        powerBtnView.setIconColor(cRedStroke)
        bottomLeftGearBtn.background = makeShapeBg(cCard, cAccentStroke, true)
        bottomLeftGearBtn.setIconColor(cText)
        bottomLeftGearBtn.setGearHoleColor(cCard)
        for (btn in roundIconBtns) {
            btn.background = makeShapeBg(cBtn, cBtnStroke, true)
            btn.setIconColor(cText)
        }

        scanDialogCardView.background = makeCardBg(cCard, cBtnStroke, 26)
        (scanIndicatorView.background as? GradientDrawable)?.setColor(cAccentStroke)
        scanTitleView.setTextColor(cText)
        for (tv in listOf(scanCloseBtn, scanMessageView, scanTroublesBtn, scanTroublesTipView)) tv.setTextColor(cSubtext)
        scanTroublesTipView.background = makeCardBg(cSurface, cBtnStroke, 14)

        contactDialogCardView.background = makeCardBg(cCard, cBtnStroke, 26)
        contactTitleView.setTextColor(cText)
        styleBtn(contactIgBtn, cAccent, cAccentStroke, cAccentText, 15f, 18)
        styleBtn(contactCloseBtn, cBtn, cBtnStroke, cSubtext, 14f, 16)

        styleBtn(scanTvBtnView, cBtn, cBtnStroke, cText, 14.5f, 18)
        styleBtn(updatesBtnView, cBtn, cAccentStroke, cText, 14.5f, 18)
        styleBtn(updatesBackBtnView, cBtn, cBtnStroke, cText, 14.5f, 18)
        styleBtn(connectBtnView, cAccent, cAccentStroke, cAccentText, 16f, 18)
        styleBtn(confirmPairBtnView, cAccent, cAccentStroke, cAccentText, 15f, 18)
        styleBtn(autoConnectBtn, if (autoConnectEnabled) cBtn else cCard, cBtnStroke, if (autoConnectEnabled) cText else cSubtext, 14f, 16)
        styleBtn(resetPairBtnView, cRedSoft, cRedStroke, cText, 14f, 16)
        styleBtn(contactUsBtnView, cBtn, cAccentStroke, cText, 14.5f, 16)

        applyTextsAndState()
        if (switchTab) show(currentScreen)
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

    private fun openContactModal() {
        contactModalOpen = true
        contactBackdropView.visibility = View.VISIBLE
    }

    private fun closeContactModal() {
        contactModalOpen = false
        contactBackdropView.visibility = View.GONE
    }

    private fun disconnectTv() {
        manualDisconnect = true; ready = false; connectedHost = null
        val cur = remote; remote = null
        fastIo.execute { cur?.close() }
        uiState(StatusState.DISCONNECTED, cMuted); updateRemoteHeaderIndicator()
        if (scanModalOpen && scannedIps.isNotEmpty()) rebuildFoundTvCards()
    }

    private fun buildContactModal() {
        contactTitleView = TextView(this).apply {
            text = t("contactOptionsTitle"); typeface = Typeface.DEFAULT_BOLD
            setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(18f))
            layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT, 0f, 0, 0, 0, 16)
        }
        contactIgBtn = Button(this).apply {
            text = t("openInstagram")
            layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, px(52), 0f, 0, 0, 0, 10)
            setOnClickListener { tap(v = this); closeContactModal(); openInstagram() }
        }
        contactCloseBtn = Button(this).apply {
            text = t("close")
            layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, px(46))
            setOnClickListener { tap(v = this); closeContactModal() }
        }
        contactDialogCardView = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL; setPadding(px(20), px(20), px(20), px(20))
            layoutParams = FrameLayout.LayoutParams(FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.WRAP_CONTENT, Gravity.CENTER).apply { setMargins(px(28), px(28), px(28), px(28)) }
            addView(contactTitleView); addView(contactIgBtn); addView(contactCloseBtn)
            setOnClickListener {}
        }
        contactBackdropView = FrameLayout(this).apply {
            visibility = View.GONE; setBackgroundColor(Color.parseColor("#B3000000")); isClickable = true
            layoutParams = FrameLayout.LayoutParams(FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.MATCH_PARENT)
            setOnClickListener { closeContactModal() }; addView(contactDialogCardView)
        }
    }

    private fun buildScanModal(prefs: android.content.SharedPreferences) {
        scanTitleView = TextView(this).apply { text = t("scanModalTitle"); typeface = Typeface.DEFAULT_BOLD; setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(18f)); layoutParams = lp(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f) }
        scanCloseBtn = Button(this).apply {
            text = "X"; background = null; setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(16f)); typeface = Typeface.DEFAULT_BOLD; isAllCaps = false
            minWidth = 0; minimumWidth = 0; minHeight = 0; minimumHeight = 0; setPadding(px(8), px(4), px(8), px(4))
            layoutParams = lp(LinearLayout.LayoutParams.WRAP_CONTENT, LinearLayout.LayoutParams.WRAP_CONTENT)
            setOnClickListener { tap(v = this); closeScanModal() }
        }
        val header = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL
            layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT, 0f, 0, 0, 0, 14)
            addView(scanTitleView); addView(scanCloseBtn)
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
            setOnClickListener {}
        }
        scanBackdropView = FrameLayout(this).apply {
            visibility = View.GONE; setBackgroundColor(Color.parseColor("#B3000000")); isClickable = true
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

    private fun renderCrashScreen(savedInstanceState: Bundle?, e: Throwable) {
        val box = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setBackgroundColor(Color.BLACK)
            setPadding(36, 64, 36, 36)
            addView(TextView(this@MainActivity).apply {
                text = "Açılış hatası [adım: $step]\n${e.javaClass.simpleName}: ${e.message ?: ""}"
                setTextColor(Color.WHITE)
                textSize = 13f
                setPadding(0, 0, 0, 24)
            })
            addView(Button(this@MainActivity).apply {
                text = t("retry")
                setOnClickListener { recreate() }
            })
        }
        setContentView(box)
        if (savedInstanceState != null) {
            step = "yeniden deneme"
        }
    }

    @SuppressLint("ClickableViewAccessibility")
    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        isActivityActive = true
        try {
            step = "tercihler"
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

            step = "giriş ve durum bileşenleri"
            ipBox = styledEdit("192.168.0.42", 17f, 18, 15, lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT, 0f, 0, 0, 0, 12)).apply { setText(prefs.getString("ip", "")) }
            codeBox = styledEdit(t("codeHint"), 16f, 16, 14, lp(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f, 0, 0, 10, 0))
            confirmPairBtnView = Button(this).apply { text = t("confirm"); layoutParams = lp(LinearLayout.LayoutParams.WRAP_CONTENT, px(54)); setOnClickListener { tap(v = this); finishPairing(codeBox.text.toString()) } }
            codeRow = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL; visibility = View.GONE; setPadding(0, px(12), 0, 0); addView(codeBox); addView(confirmPairBtnView) }

            statusDot = View(this).apply { layoutParams = lp(px(10), px(10), 0f, 0, 0, 10, 0); background = GradientDrawable().apply { shape = GradientDrawable.OVAL; setColor(cMuted) } }
            status = TextView(this).apply {
                text = formatStatus(lastStatusState, null)
                setTextColor(cSubtext)
                setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(13f))
                maxLines = 6
                setLineSpacing(px(2).toFloat(), 1.1f)
                layoutParams = lp(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f)
            }

            step = "kumanda ekranı"
            powerBtnView = RemoteIconButton(this, IconKind.POWER).apply {
                layoutParams = lp(px(50), px(50))
                applyPressAnim(this)
                setOnClickListener { tap(v = this); sendKey(26) }
            }
            remoteHeaderDot = View(this).apply { layoutParams = lp(px(9), px(9), 0f, 10, 0, 8, 0); background = GradientDrawable().apply { shape = GradientDrawable.OVAL; setColor(cMuted) } }
            remoteHeaderTvName = TextView(this).apply { text = t("tvDeviceFallback"); typeface = Typeface.DEFAULT_BOLD; setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(15f)); setSingleLine(); layoutParams = lp(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f) }

            bottomLeftGearBtn = RemoteIconButton(this, IconKind.IOS_SETTINGS).apply {
                layoutParams = lp(px(52), px(52))
                applyPressAnim(this)
                setOnClickListener { tap(v = this); show(2) }
            }

            val initialSize = wheelSizes[wheelSizeMode].second.second
            dpadWheelView = DpadWheelView(this) { zone ->
                tap(v = dpadWheelView)
                when (zone) { DpadZone.UP -> sendKey(19); DpadZone.RIGHT -> sendKey(22); DpadZone.DOWN -> sendKey(20); DpadZone.LEFT -> sendKey(21); DpadZone.CENTER -> sendKey(23); DpadZone.NONE -> Unit }
            }.apply { layoutParams = LinearLayout.LayoutParams(px(initialSize), px(initialSize)).apply { setMargins(0, px(8), 0, px(8)) } }

            val remoteHeaderRow = LinearLayout(this).apply {
                orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL
                layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, px(56), 0f, 0, 2, 0, 12)
                addView(powerBtnView); addView(remoteHeaderDot); addView(remoteHeaderTvName)
            }
            val volumeRow = LinearLayout(this).apply {
                orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER
                layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, px(64), 0f, 0, 2, 0, 12)
                addView(roundIconKey(IconKind.MUTE, 56) { sendKey(164) })
                addView(View(this@MainActivity).apply { layoutParams = lp(px(14), px(1)) })
                addView(roundIconKey(IconKind.VOL_DOWN, 56) { sendKey(25) })
                addView(View(this@MainActivity).apply { layoutParams = lp(px(14), px(1)) })
                addView(roundIconKey(IconKind.VOL_UP, 56) { sendKey(24) })
                addView(View(this@MainActivity).apply { layoutParams = lp(px(14), px(1)) })
                addView(roundIconKey(IconKind.RECONNECT, 56) { manualDisconnect = false; connectClicked() })
            }
            val bottomKeysRow = LinearLayout(this).apply {
                orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER
                layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, px(62), 0f, 0, 6, 0, 6)
                addView(roundIconKey(IconKind.BACK, 54) { sendKey(4) })
                addView(View(this@MainActivity).apply { layoutParams = lp(px(36), px(1)) })
                addView(roundIconKey(IconKind.HOME, 54) { sendKey(3) })
            }

            screens.add(LinearLayout(this).apply {
                orientation = LinearLayout.VERTICAL; gravity = Gravity.CENTER_HORIZONTAL; visibility = View.GONE; setPadding(px(14), px(6), px(14), px(6))
                addView(remoteHeaderRow)
                addView(volumeRow)
                addView(dpadWheelView)
                addView(View(this@MainActivity).apply { layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, 0, 1f) })
                addView(bottomKeysRow)
            })

            step = "bağlantı ekranı"
            connectBtnView = Button(this).apply {
                text = t("connect"); layoutParams = lp(0, px(58), 1f, 0, 0, 6, 0)
                setOnClickListener {
                    tap(v = this)
                    val trimmed = ipBox.text.toString().trim()
                    if (!isValidIpv4(trimmed)) { uiState(StatusState.ENTER_IP, cRedStroke); return@setOnClickListener }
                    manualDisconnect = false
                    prefs.edit().putString("ip", trimmed).apply()
                    if (prefs.getBoolean("paired", false)) connectClicked() else startPairing()
                }
            }
            scanTvBtnView = Button(this).apply {
                text = t("scanTv"); layoutParams = lp(0, px(58), 1f, 6, 0, 0, 0)
                setOnClickListener { tap(v = this); openAndScanNetwork(prefs) }
            }
            tvIpTitleView = sectionTitle(t("tvIp"), 18f, 10)
            connectCardView = LinearLayout(this).apply {
                orientation = LinearLayout.VERTICAL; setPadding(px(16), px(18), px(16), px(18)); layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT)
                addView(tvIpTitleView); addView(ipBox); addView(row(connectBtnView, scanTvBtnView).apply { layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT) }); addView(codeRow)
            }
            screens.add(ScrollView(this).apply {
                visibility = View.GONE
                addView(LinearLayout(this@MainActivity).apply {
                    orientation = LinearLayout.VERTICAL; gravity = Gravity.CENTER_HORIZONTAL; setPadding(px(14), px(10), px(14), px(12))
                    addView(connectCardView)
                })
            })

            step = "ayarlar ekranı"
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
                    val r = optionRow(t("sizeMedium"), null) { wheelSizeMode = mode; prefs.edit().putInt("wheel_size", mode).apply(); sizeDropdownOpen = false; val p = px(wheelSizes[mode].second.second); dpadWheelView.layoutParams = LinearLayout.LayoutParams(p, p).apply { setMargins(0, px(8), 0, px(8)) }; refreshDropdowns() }
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

            updatesBtnView = Button(this).apply {
                text = t("updates")
                layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, px(50), 0f, 0, 12, 0, 0)
                setOnClickListener { tap(v = this); rebuildReleaseNotes(); show(3) }
            }
            resetPairBtnView = Button(this).apply {
                text = t("resetPair"); layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, px(50), 0f, 0, 8, 0, 0)
                setOnClickListener {
                    tap(v = this)
                    prefs.edit().putBoolean("paired", false).apply()
                    File(filesDir, "client.key").delete()
                    File(filesDir, "client.crt").delete()
                    identity = null
                    manualDisconnect = true
                    val oldPair = pairConn; val oldRemote = remote
                    pairConn = null; pairServerCert = null; remote = null; connectedHost = null; ready = false
                    fastIo.execute { oldPair?.close(); oldRemote?.close() }
                    codeRow.visibility = View.GONE; uiState(StatusState.PAIR_RESET, cMuted); updateRemoteHeaderIndicator()
                }
            }
            contactUsBtnView = Button(this).apply {
                text = t("contactUs"); layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, px(50), 0f, 0, 8, 0, 0)
                setOnClickListener { tap(v = this); openContactModal() }
            }
            settingsTitleView = sectionTitle(t("settings"), 17.5f, 6)

            settingsCardView = LinearLayout(this).apply {
                orientation = LinearLayout.VERTICAL; setPadding(px(16), px(16), px(16), px(16))
                layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT)
                addView(settingsTitleView); addView(vibHeaderRow); addView(vibOptionsContainer); addView(sizeHeaderRow); addView(sizeOptionsContainer)
                addView(autoConnectBtn); addView(paletteHeaderRow); addView(paletteOptionsContainer); addView(langHeaderRow); addView(langOptionsContainer)
                addView(updatesBtnView); addView(resetPairBtnView); addView(contactUsBtnView)
            }
            screens.add(ScrollView(this).apply {
                visibility = View.GONE
                addView(LinearLayout(this@MainActivity).apply {
                    orientation = LinearLayout.VERTICAL; gravity = Gravity.CENTER_HORIZONTAL; setPadding(px(14), px(10), px(14), px(12))
                    addView(settingsCardView)
                })
            })

            step = "güncellemeler ekranı"
            updatesTitleView = sectionTitle(t("updatesTitle"), 18f, 10)
            updatesListContainer = LinearLayout(this).apply {
                orientation = LinearLayout.VERTICAL
                layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT, 0f, 0, 4, 0, 8)
            }
            updatesBackBtnView = Button(this).apply {
                text = t("back")
                layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, px(50), 0f, 0, 4, 0, 0)
                setOnClickListener { tap(v = this); show(2) }
            }
            updatesCardView = LinearLayout(this).apply {
                orientation = LinearLayout.VERTICAL; setPadding(px(16), px(18), px(16), px(18))
                layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT)
                addView(updatesTitleView)
                addView(updatesListContainer)
                addView(updatesBackBtnView)
            }
            screens.add(ScrollView(this).apply {
                visibility = View.GONE
                addView(LinearLayout(this@MainActivity).apply {
                    orientation = LinearLayout.VERTICAL; gravity = Gravity.CENTER_HORIZONTAL; setPadding(px(14), px(10), px(14), px(12))
                    addView(updatesCardView)
                })
            })

            step = "kabuk ve yerleşim"
            topBarView = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL; setPadding(px(16), px(11), px(16), px(11)); layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT, 0f, 14, 2, 14, 6); addView(statusDot); addView(status) }
            val content = FrameLayout(this).apply {
                layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, 0, 1f)
                for (sc in screens) addView(sc, FrameLayout.LayoutParams(FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.MATCH_PARENT))
                addView(bottomLeftGearBtn, FrameLayout.LayoutParams(px(52), px(52), Gravity.BOTTOM or Gravity.START).apply {
                    setMargins(px(22), 0, 0, px(12))
                })
            }
            val bottomNav = row(nav(t("tabRemote"), 0), nav(t("tabConnect"), 1)).apply { setPadding(px(8), px(2), px(8), px(4)) }
            this@MainActivity.rootView = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL; setPadding(px(4), px(26), px(4), px(6)); addView(topBarView); addView(content); addView(bottomNav) }

            step = "pencere katmanları"
            buildScanModal(prefs)
            buildContactModal()
            val shell = FrameLayout(this)
            shell.addView(this@MainActivity.rootView, FrameLayout.LayoutParams(FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.MATCH_PARENT))
            shell.addView(scanBackdropView, FrameLayout.LayoutParams(FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.MATCH_PARENT))
            shell.addView(contactBackdropView, FrameLayout.LayoutParams(FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.MATCH_PARENT))

            setContentView(shell)

            step = "başlangıç durumu"
            currentScreen = if (paired && isValidIpv4(ipBox.text.toString().trim())) 0 else 1
            applyPalette(paletteIndex, switchTab = false)
            show(currentScreen)
            if (currentScreen == 0 && autoConnectEnabled) connectClicked()
        } catch (e: Throwable) {
            renderCrashScreen(savedInstanceState, e)
        }
    }

    override fun onStart() {
        super.onStart()
        isActivityActive = true
    }

    @Deprecated("Deprecated in Java")
    override fun onBackPressed() {
        if (contactModalOpen) { closeContactModal(); return }
        if (scanModalOpen) { closeScanModal(); return }
        if (currentScreen == 3) { show(2); return }
        @Suppress("DEPRECATION") super.onBackPressed()
    }

    private fun openInstagram() {
        val uri = Uri.parse(instagramUrl)
        try {
            startActivity(Intent(Intent.ACTION_VIEW, uri).apply { setPackage("com.instagram.android") })
        } catch (_: Exception) {
            try {
                startActivity(Intent(Intent.ACTION_VIEW, uri))
            } catch (_: Exception) {
                Toast.makeText(this, t("linkOpenFailed"), Toast.LENGTH_SHORT).show()
            }
        }
    }

    private fun intIpToPrefix(ipInt: Int): String? {
        if (ipInt == 0) return null
        val b1 = ipInt and 0xFF
        val b2 = (ipInt ushr 8) and 0xFF
        val b3 = (ipInt ushr 16) and 0xFF
        if (b1 == 0 || b1 == 127) return null
        return "$b1.$b2.$b3"
    }

    private fun isPrivateLanIpv4(ip: String): Boolean {
        val parts = ip.split(".")
        if (parts.size != 4) return false
        val a = parts[0].toIntOrNull() ?: return false
        val b = parts[1].toIntOrNull() ?: return false
        return a == 192 && b == 168 || a == 10 || (a == 172 && b in 16..31)
    }

    private fun getLocalSubnetPrefix(): String? {
        try {
            val cm = getSystemService(Context.CONNECTIVITY_SERVICE) as ConnectivityManager
            val net = findWifiNetwork() ?: cm.activeNetwork
            if (net != null) {
                val prefix = cm.getLinkProperties(net)?.linkAddresses?.firstNotNullOfOrNull { linkAddr ->
                    val addr = linkAddr.address
                    val hostAddr = addr.hostAddress
                    if (addr is Inet4Address && !addr.isLoopbackAddress && hostAddr != null && isPrivateLanIpv4(hostAddr)) {
                        hostAddr.split(".").take(3).joinToString(".")
                    } else null
                }
                if (!prefix.isNullOrBlank()) return prefix
            }
        } catch (_: Exception) {}
        try {
            @Suppress("DEPRECATION")
            val wifi = applicationContext.getSystemService(Context.WIFI_SERVICE) as? WifiManager
            @Suppress("DEPRECATION")
            val p = intIpToPrefix(wifi?.connectionInfo?.ipAddress ?: 0)
            if (!p.isNullOrBlank() && isPrivateLanIpv4("$p.1")) return p
        } catch (_: Exception) {}
        return try {
            val ifaces = NetworkInterface.getNetworkInterfaces() ?: return null
            while (ifaces.hasMoreElements()) {
                val iface = ifaces.nextElement()
                if (!iface.isUp || iface.isLoopback) continue
                val addrs = iface.inetAddresses
                while (addrs.hasMoreElements()) {
                    val addr = addrs.nextElement()
                    val h = addr.hostAddress
                    if (addr is Inet4Address && !addr.isLoopbackAddress && h != null && isPrivateLanIpv4(h)) {
                        return h.split(".").take(3).joinToString(".")
                    }
                }
            }
            null
        } catch (_: Exception) { null }
    }

    private fun buildFoundTvCard(prefs: android.content.SharedPreferences, ip: String): LinearLayout {
        val isDeviceConnected = (ready && remote != null && connectedHost == ip)
        return LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL; setPadding(px(14), px(12), px(14), px(12))
            layoutParams = lp(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT, 0f, 0, 0, 0, 10)
            background = makeCardBg(cSurface, if (isDeviceConnected) cGreen else cBtnStroke, 18)
            addView(LinearLayout(this@MainActivity).apply {
                orientation = LinearLayout.VERTICAL; layoutParams = lp(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f, 0, 0, 8, 0)
                addView(TextView(this@MainActivity).apply { text = t("tvDeviceFallback"); typeface = Typeface.DEFAULT_BOLD; setTextColor(cText); setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(14.5f)); setSingleLine() })
                addView(TextView(this@MainActivity).apply { text = ip; setTextColor(cSubtext); setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(12.5f)); setSingleLine(); layoutParams = lp(LinearLayout.LayoutParams.WRAP_CONTENT, LinearLayout.LayoutParams.WRAP_CONTENT, 0f, 0, 2, 0, 0) })
            })
            if (isDeviceConnected) {
                addView(Button(this@MainActivity).apply {
                    text = "X ${t("disconnect")}"; layoutParams = lp(LinearLayout.LayoutParams.WRAP_CONTENT, px(38))
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
            val latch = CountDownLatch(254)
            val pool = Executors.newFixedThreadPool(24)
            try {
                for (lastOctet in 1..254) {
                    if (token != scanToken || !isActivityActive) { latch.countDown(); continue }
                    pool.execute {
                        try {
                            if (token == scanToken && isActivityActive) {
                                val candidate = "$prefix.$lastOctet"
                                if ((isTvPortOpen(candidate, 6466, 300) || isTvPortOpen(candidate, 6467, 300)) && token == scanToken && !found.contains(candidate)) {
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
                latch.await(8500, TimeUnit.MILLISECONDS)
            } finally {
                pool.shutdownNow()
            }
            if (token != scanToken || !isActivityActive) return@execute

            val uniqueIps = found.distinct().sortedBy { it.substringAfterLast(".").toIntOrNull() ?: 999 }
            runOnUiThread {
                if (token != scanToken || !isActivityActive) return@runOnUiThread
                scannedIps.clear(); scannedIps.addAll(uniqueIps); rebuildFoundTvCards()
                setScanBusy(false)
                if (uniqueIps.isEmpty()) { scanMessageView.text = t(StatusState.SCAN_NONE.name); uiState(StatusState.SCAN_NONE, cRedStroke) }
                else { scanMessageView.text = "${t(StatusState.SCAN_FOUND.name)} (${uniqueIps.size})"; uiState(StatusState.SCAN_FOUND, cGreen, uniqueIps.first()) }
            }
        }
    }

    private fun isTvPortOpen(ip: String, port: Int, timeoutMs: Int): Boolean = try {
        Socket().use {
            bindSocketToWifi(it)
            it.connect(InetSocketAddress(ip, port), timeoutMs)
            true
        }
    } catch (_: Exception) { false }

    private fun nav(label: String, i: Int) = Button(this).apply {
        text = label; typeface = Typeface.DEFAULT_BOLD; isAllCaps = false; setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(14.5f))
        setPadding(px(6), px(2), px(6), px(2)); layoutParams = lp(0, px(56), 1f, 5, 2, 5, 4)
        navBtns.add(this); applyPressAnim(this); setOnClickListener { tap(v = this); show(i) }
    }

    private fun row(vararg views: View) = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER; for (v in views) addView(v) }

    private fun roundIconKey(kind: IconKind, sizeDp: Int, onClick: () -> Unit): RemoteIconButton {
        val btn = RemoteIconButton(this, kind).apply {
            layoutParams = lp(px(sizeDp), px(sizeDp))
            applyPressAnim(this)
            setOnClickListener { tap(v = this); onClick() }
        }
        roundIconBtns.add(btn)
        return btn
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
        val ctx = SSLContext.getInstance("TLSv1.2").apply {
            init(arrayOf<KeyManager>(FixedKm(id)), arrayOf<TrustManager>(TrustAll()), SecureRandom())
        }
        val rawSocket = Socket().apply {
            tcpNoDelay = true
            keepAlive = true
            bindSocketToWifi(this)
            connect(InetSocketAddress(h, port), 8000)
            soTimeout = readTimeoutMs
        }
        val sslSocket = (ctx.socketFactory.createSocket(rawSocket, h, port, true) as SSLSocket).apply {
            useClientMode = true
            enabledProtocols = supportedProtocols.filter { it == "TLSv1.2" || it == "TLSv1.3" }.toTypedArray().ifEmpty { supportedProtocols }
            startHandshake()
        }
        return Conn(sslSocket)
    }

    private fun outer(field: Int, inner: ByteArray) = Pb.int(1, 2) + Pb.int(2, 200) + Pb.bytes(field, inner)

    private fun expect(c: Conn, field: Int) {
        while (true) {
            val m = Pb.parse(c.read())
            val st = m.firstOrNull { it.num == 2 }?.number
            if (st != null && st != 200L && st != 0L) throw IllegalStateException("TV eşleştirmeyi reddetti ($st)")
            if (m.any { it.num == field }) return
        }
    }

    private fun startPairing() {
        val h = ipBox.text.toString().trim()
        if (!isValidIpv4(h)) { uiState(StatusState.ENTER_IP, cRedStroke); return }
        host = h
        runOnUiThread { codeRow.visibility = View.GONE }
        val oldPair: Conn? = synchronized(pairLock) {
            val prev = pairConn
            pairConn = null
            pairServerCert = null
            prev
        }
        fastIo.execute { oldPair?.close() }
        uiState(StatusState.PAIRING_START, cAccentStroke)
        fastIo.execute {
            try {
                val c = openTls(h, 6467, identity(), 15000)
                val cert = c.sock.session.peerCertificates.firstOrNull() as? X509Certificate
                    ?: throw IllegalStateException("TV sertifikası alınamadı")
                c.send(outer(10, Pb.str(1, "atvremote") + Pb.str(2, "Android TV Remote"))); expect(c, 11)
                c.send(outer(20, Pb.bytes(1, Pb.int(1, 3) + Pb.int(2, 6)) + Pb.int(3, 1))); expect(c, 20)
                c.send(outer(30, Pb.bytes(1, Pb.int(1, 3) + Pb.int(2, 6)) + Pb.int(2, 1))); expect(c, 31)
                synchronized(pairLock) {
                    pairConn = c
                    pairServerCert = cert
                }
                runOnUiThread { codeRow.visibility = View.VISIBLE }
                uiState(StatusState.ENTER_CODE, cAccentStroke)
            } catch (e: Exception) {
                synchronized(pairLock) {
                    pairConn = null
                    pairServerCert = null
                }
                uiState(StatusState.PAIRING_FAILED, cRedStroke, diagnoseConnectionError(e, h, 6467))
            }
        }
    }

    private fun finishPairing(raw: String) {
        val code = raw.trim().uppercase()
        if (code.length != 6) { uiState(StatusState.CODE_LENGTH, cRedStroke); return }
        fastIo.execute {
            try {
                val hexPart = code.substring(2)
                if (!hexPart.all { it in '0'..'9' || it in 'A'..'F' }) {
                    throw IllegalArgumentException("Geçersiz kod formatı")
                }
                val (c, serverCert) = synchronized(pairLock) {
                    val conn = pairConn ?: throw IllegalStateException("Eşleştirme oturumu açık değil")
                    val cert = pairServerCert ?: throw IllegalStateException("TV sertifikası alınamadı")
                    conn to cert
                }
                val id = identity()
                val clientPub = id.cert.publicKey as RSAPublicKey
                val serverPub = serverCert.publicKey as RSAPublicKey
                val secret = MessageDigest.getInstance("SHA-256").apply {
                    update(clientPub.modulus.unsigned()); update(clientPub.publicExponent.unsigned())
                    update(serverPub.modulus.unsigned()); update(serverPub.publicExponent.unsigned()); update(hexToBytes(hexPart))
                }.digest()
                c.send(outer(40, Pb.bytes(1, secret)))
                expect(c, 41)
                c.close()
                synchronized(pairLock) {
                    if (pairConn === c) {
                        pairConn = null
                        pairServerCert = null
                    }
                }
                manualDisconnect = false
                getSharedPreferences("tv", MODE_PRIVATE).edit().putBoolean("paired", true).apply()
                runOnUiThread { codeRow.visibility = View.GONE }
            } catch (e: Exception) {
                uiState(StatusState.CODE_REJECTED, cRedStroke, e.message ?: e.javaClass.simpleName)
                return@execute
            }

            uiState(StatusState.PAIRED_CONNECTING, cAccentStroke)
            try {
                connectRemote()
                runOnUiThread { show(0) }
            } catch (e: Exception) {
                uiState(StatusState.CONNECT_FAILED, cRedStroke, diagnoseConnectionError(e, host, 6466))
            }
        }
    }

    private fun connectClicked() {
        val h = ipBox.text.toString().trim()
        if (!isValidIpv4(h)) { uiState(StatusState.ENTER_IP, cRedStroke); return }
        host = h; manualDisconnect = false; uiState(StatusState.CONNECTING, cAccentStroke)
        fastIo.execute {
            try { connectRemote(); runOnUiThread { show(0) } }
            catch (e: Exception) { uiState(StatusState.CONNECT_FAILED, cRedStroke, diagnoseConnectionError(e, h, 6466)) }
        }
    }

    private fun connectRemote() {
        synchronized(connectLock) {
            ready = false
            val old = remote
            remote = null
            old?.close()
            val c = openTls(host, 6466, identity(), 0)
            remote = c
            connectedHost = host
            fastIo.execute { readerLoop(c) }
            waitReady()
        }
    }

    private fun waitReady() {
        var waited = 0
        while (!ready && waited < 4500) {
            Thread.sleep(15)
            waited += 15
        }
        if (!ready) {
            val cur = remote
            remote = null
            connectedHost = null
            cur?.close()
            throw IllegalStateException("TV hazır sinyali göndermedi")
        }
    }

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
                        40 -> {
                            ready = true
                            uiState(StatusState.CONNECTED, cGreen)
                            if (scanModalOpen && scannedIps.isNotEmpty()) runOnUiThread { rebuildFoundTvCards() }
                        }
                    }
                }
            }
        } catch (e: Exception) {
            if (remote === c) {
                remote = null; ready = false; connectedHost = null
                if (!manualDisconnect && isActivityActive) {
                    uiState(StatusState.LOST, cRedStroke, e.message ?: e.javaClass.simpleName)
                    if (autoConnectEnabled && isValidIpv4(host)) {
                        fastIo.execute {
                            try {
                                Thread.sleep(1200L)
                                if (!manualDisconnect && isActivityActive && remote == null && isValidIpv4(host)) {
                                    uiState(StatusState.CONNECTING, cAccentStroke)
                                    connectRemote()
                                }
                            } catch (_: Exception) {}
                        }
                    }
                }
            }
        }
    }

    private fun writeKey(code: Int) {
        val effectiveHost = host.ifBlank { ipBox.text.toString().trim() }
        if (effectiveHost.isNotBlank() && host.isBlank()) host = effectiveHost
        val msg = Pb.bytes(10, Pb.int(1, code) + Pb.int(2, 3))
        val c = remote
        if (c != null && ready) {
            try {
                c.send(msg)
                return
            } catch (_: Exception) {
                remote = null; ready = false
            }
        }
        if (!isValidIpv4(effectiveHost)) throw IllegalStateException(t(StatusState.ENTER_IP.name))
        synchronized(connectLock) {
            if (remote == null || !ready) {
                val now = System.currentTimeMillis()
                if (now - lastConnectAttemptMs < 2500L) {
                    throw IllegalStateException("Bağlantı kurulamıyor, tekrar deneyin")
                }
                lastConnectAttemptMs = now
                connectRemote()
            }
        }
        val active = remote
        if (active == null || !ready) {
            throw IllegalStateException(t(StatusState.CONNECT_FAILED.name))
        }
        active.send(msg)
    }

    private fun sendKey(code: Int) = fastIo.execute {
        try { writeKey(code) }
        catch (e: Exception) { uiState(StatusState.SEND_FAILED, cRedStroke, e.message ?: e.javaClass.simpleName) }
    }

    override fun onStop() {
        super.onStop()
        isActivityActive = false
        pulseAnim?.cancel()
    }

    override fun onDestroy() {
        super.onDestroy()
        isActivityActive = false
        pulseAnim?.cancel(); pulseAnim = null
        scanToken++
        val p = pairConn; val r = remote
        pairConn = null; pairServerCert = null; remote = null; ready = false
        p?.close(); r?.close()
        fastIo.shutdownNow()
    }
}
