package com.example.tvkumanda

import android.annotation.SuppressLint
import android.app.Activity
import android.content.res.ColorStateList
import android.graphics.Color
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
            while (true) {
                val x = b[i++].toInt() and 0xFF
                r = r or ((x and 0x7F).toLong() shl shift)
                if ((x and 0x80) == 0) break
                shift += 7
            }
            return r
        }
        while (i < b.size) {
            val key = readVar().toInt()
            val num = key ushr 3
            when (key and 7) {
                0 -> out.add(Field(num, readVar(), EMPTY))
                2 -> {
                    val len = readVar().toInt()
                    out.add(Field(num, 0, b.copyOfRange(i, i + len)))
                    i += len
                }
                1 -> i += 8
                5 -> i += 4
                else -> return out
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

private fun hexToBytes(s: String): ByteArray =
    ByteArray(s.length / 2) { s.substring(it * 2, it * 2 + 2).toInt(16).toByte() }

class MainActivity : Activity() {

    private val fastIo = Executors.newCachedThreadPool()
    private var identity: Identity? = null
    private var remote: Conn? = null
    @Volatile private var ready = false
    @Volatile private var reconnecting = false
    private var pairConn: Conn? = null
    private var pairServerCert: X509Certificate? = null
    private var host = ""

    private lateinit var statusDot: View
    private lateinit var status: TextView
    private lateinit var ipBox: EditText
    private lateinit var codeBox: EditText
    private lateinit var codeRow: LinearLayout
    private lateinit var textBox: EditText
    private var dp = 1f
    private var sp = 1f
    private val navBtns = ArrayList<Button>()

    private val cBg = Color.parseColor("#0E1015")
    private val cCard = Color.parseColor("#171A22")
    private val cBtn = Color.parseColor("#222733")
    private val cBtnStroke = Color.parseColor("#32394A")
    private val cAccent = Color.parseColor("#3B82F6")
    private val cAccentStroke = Color.parseColor("#60A5FA")
    private val cRed = Color.parseColor("#EF4444")
    private val cRedStroke = Color.parseColor("#F87171")
    private val cGreen = Color.parseColor("#22C55E")
    private val cMuted = Color.parseColor("#64748B")
    private val cText = Color.parseColor("#F8FAFC")

    private fun px(v: Int) = (v * dp).toInt()
    private fun scaledSp(v: Float) = v * (sp / dp).coerceIn(0.85f, 1.35f)

    private val screens = ArrayList<View>()

    private fun screen(vararg v: View) = LinearLayout(this).apply {
        orientation = LinearLayout.VERTICAL
        gravity = Gravity.CENTER_VERTICAL
        visibility = View.GONE
        setPadding(px(14), px(6), px(14), px(6))
        v.forEach { addView(it) }
        screens.add(this)
    }

    private fun show(i: Int) {
        screens.forEachIndexed { n, sc -> sc.visibility = if (n == i) View.VISIBLE else View.GONE }
        navBtns.forEachIndexed { n, b ->
            val active = n == i
            b.background = makeButtonBg(if (active) cAccent else cCard, if (active) cAccentStroke else cBtnStroke, 14)
            b.setTextColor(if (active) Color.WHITE else Color.parseColor("#CBD5E1"))
        }
    }

    private fun nav(label: String, i: Int) = Button(this).apply {
        text = label
        setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(13f))
        isAllCaps = false
        setPadding(px(4), px(2), px(4), px(2))
        layoutParams = lp(50)
        navBtns.add(this)
        setOnClickListener {
            performHapticFeedback(HapticFeedbackConstants.KEYBOARD_TAP)
            show(i)
        }
    }

    private fun makeButtonBg(fill: Int, stroke: Int, radiusDp: Int): RippleDrawable {
        val shape = GradientDrawable().apply {
            cornerRadius = px(radiusDp).toFloat()
            setColor(fill)
            setStroke(px(1), stroke)
        }
        val rippleColor = ColorStateList.valueOf(Color.parseColor("#40FFFFFF"))
        return RippleDrawable(rippleColor, shape, null)
    }

    private fun makeInputBg(): GradientDrawable = GradientDrawable().apply {
        cornerRadius = px(14).toFloat()
        setColor(cCard)
        setStroke(px(1), cBtnStroke)
    }

    @SuppressLint("ClickableViewAccessibility")
    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        dp = resources.displayMetrics.density
        sp = resources.displayMetrics.scaledDensity
        val prefs = getSharedPreferences("tv", MODE_PRIVATE)
        val paired = prefs.getBoolean("paired", false)

        ipBox = EditText(this).apply {
            hint = "TV IP (örn. 192.168.1.105)"
            setHintTextColor(cMuted)
            setTextColor(cText)
            setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(15f))
            background = makeInputBg()
            setPadding(px(14), px(12), px(14), px(12))
            setText(prefs.getString("ip", ""))
            setSingleLine()
            layoutParams = LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT
            ).apply { setMargins(px(4), px(4), px(4), px(8)) }
        }
        codeBox = EditText(this).apply {
            hint = "6 haneli kod"
            setHintTextColor(cMuted)
            setTextColor(cText)
            setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(15f))
            background = makeInputBg()
            setPadding(px(14), px(12), px(14), px(12))
            setSingleLine()
            layoutParams = LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f).apply {
                setMargins(px(4), px(4), px(6), px(4))
            }
        }
        codeRow = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER_VERTICAL
            visibility = View.GONE
            setPadding(0, px(8), 0, 0)
            addView(codeBox)
            addView(Button(this@MainActivity).apply {
                text = "Onayla"
                style(this, cAccent, cAccentStroke, 15f)
                layoutParams = LinearLayout.LayoutParams(
                    LinearLayout.LayoutParams.WRAP_CONTENT, px(50)
                ).apply { setMargins(px(4), px(4), px(4), px(4)) }
                setOnClickListener { finishPairing(codeBox.text.toString()) }
            })
        }
        statusDot = View(this).apply {
            layoutParams = LinearLayout.LayoutParams(px(10), px(10)).apply {
                setMargins(0, 0, px(8), 0)
            }
            background = GradientDrawable().apply {
                shape = GradientDrawable.OVAL
                setColor(cMuted)
            }
        }
        status = TextView(this).apply {
            text = if (paired) "Bağlı değil" else "Önce TV'nin IP adresini yaz"
            setTextColor(Color.parseColor("#CBD5E1"))
            setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(13.5f))
            setSingleLine()
        }
        textBox = EditText(this).apply {
            hint = "TV'ye yazılacak metin (a-z, 0-9)"
            setHintTextColor(cMuted)
            setTextColor(cText)
            setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(16f))
            background = makeInputBg()
            setPadding(px(16), px(14), px(16), px(14))
            setSingleLine()
            layoutParams = LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT
            ).apply { setMargins(px(4), px(4), px(4), px(12)) }
        }

        screen(
            row(gap(), key("▲", 19, sizeSp = 19f), gap()),
            row(key("◀", 21, sizeSp = 19f), key("OK", 23, cAccent, cAccentStroke, 17f), key("▶", 22, sizeSp = 19f)),
            row(gap(), key("▼", 20, sizeSp = 19f), gap()),
            row(key("Geri", 4, sizeSp = 14.5f), key("Ana", 3, sizeSp = 14.5f), key("Ayarlar", 176, sizeSp = 14.5f)),
            row(key("Ses −", 25, sizeSp = 15f), key("Sessiz", 164, sizeSp = 14.5f), key("Ses +", 24, sizeSp = 15f)),
            row(key("⏯", 85, sizeSp = 18f), key("Aç/Kapat", 26, cRed, cRedStroke, 15f))
        )
        screen(
            TextView(this).apply {
                text = "Hızlı Metin"
                setTextColor(cText)
                setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(20f))
                setPadding(px(4), 0, 0, px(8))
            },
            textBox,
            row(
                Button(this).apply {
                    text = "Gönder"
                    style(this, cAccent, cAccentStroke, 15.5f)
                    layoutParams = lp(62)
                    setOnClickListener {
                        performHapticFeedback(HapticFeedbackConstants.KEYBOARD_TAP)
                        sendText(textBox.text.toString())
                    }
                },
                key("Sil", 67, sizeSp = 15f),
                key("Enter", 66, sizeSp = 15f)
            )
        )
        screen(
            TextView(this).apply {
                text = "Bağlantı"
                setTextColor(cText)
                setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(20f))
                setPadding(px(4), 0, 0, px(10))
            },
            ipBox,
            row(
                Button(this).apply {
                    text = "Eşleştir"
                    style(this, cBtn, cBtnStroke, 15f)
                    layoutParams = lp(52)
                    setOnClickListener {
                        performHapticFeedback(HapticFeedbackConstants.KEYBOARD_TAP)
                        prefs.edit().putString("ip", ipBox.text.toString().trim()).apply()
                        startPairing()
                    }
                },
                Button(this).apply {
                    text = "Bağlan"
                    style(this, cAccent, cAccentStroke, 15f)
                    layoutParams = lp(52)
                    setOnClickListener {
                        performHapticFeedback(HapticFeedbackConstants.KEYBOARD_TAP)
                        prefs.edit().putString("ip", ipBox.text.toString().trim()).apply()
                        connectClicked()
                    }
                }
            ),
            codeRow
        )

        val topBar = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER_VERTICAL
            background = GradientDrawable().apply {
                cornerRadius = px(14).toFloat()
                setColor(cCard)
                setStroke(px(1), cBtnStroke)
            }
            setPadding(px(14), px(10), px(14), px(10))
            layoutParams = LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT
            ).apply { setMargins(px(10), 0, px(10), px(6)) }
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

        val root = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setBackgroundColor(cBg)
            setPadding(px(6), px(28), px(6), px(8))
            addView(topBar)
            addView(content)
            addView(row(nav("Kumanda", 0), nav("Klavye", 1), nav("Bağlantı", 2)))
        }
        setContentView(root)

        if (paired && ipBox.text.isNotBlank()) {
            show(0)
            connectClicked()
        } else {
            show(2)
        }
    }

    private fun lp(h: Int = 66) = LinearLayout.LayoutParams(0, px(h), 1f).apply {
        setMargins(px(5), px(5), px(5), px(5))
    }

    private fun style(b: Button, fill: Int, stroke: Int, sizeSp: Float) {
        b.background = makeButtonBg(fill, stroke, 16)
        b.setTextColor(cText)
        b.isAllCaps = false
        b.setTextSize(TypedValue.COMPLEX_UNIT_SP, scaledSp(sizeSp))
        b.setPadding(px(4), px(2), px(4), px(2))
    }

    private fun row(vararg views: View) = LinearLayout(this).apply {
        orientation = LinearLayout.HORIZONTAL
        gravity = Gravity.CENTER_VERTICAL
        views.forEach { addView(it) }
    }

    private fun key(label: String, code: Int, fill: Int = cBtn, stroke: Int = cBtnStroke, sizeSp: Float = 16f) = Button(this).apply {
        text = label
        style(this, fill, stroke, sizeSp)
        layoutParams = lp()
        setOnClickListener {
            performHapticFeedback(HapticFeedbackConstants.VIRTUAL_KEY)
            sendKey(code)
        }
    }

    private fun gap() = View(this).apply { layoutParams = lp() }

    private fun ui(s: String, dotColor: Int = cMuted) = runOnUiThread {
        status.text = s
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
        s.connect(InetSocketAddress(h, port), 4000)
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
            ui("Önce TV'nin IP adresini yaz", cRed)
            return
        }
        host = h
        ui("Eşleştirme başlıyor…", cAccent)
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
                ui("TV'deki 6 haneli kodu yazıp Onayla'ya bas", cAccent)
            } catch (e: Exception) {
                ui("Eşleştirme başarısız: ${e.message}", cRed)
            }
        }
    }

    private fun finishPairing(raw: String) {
        val code = raw.trim().uppercase()
        if (code.length != 6) {
            ui("Kod 6 karakter olmalı", cRed)
            return
        }
        fastIo.execute {
            try {
                val c = pairConn ?: throw IllegalStateException("Önce Eşleştir'e bas")
                val id = identity()
                val clientPub = id.cert.publicKey as RSAPublicKey
                val serverPub = pairServerCert!!.publicKey as RSAPublicKey
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
                ui("Eşleşti — Bağlanıyor…", cAccent)
                connectRemote()
                runOnUiThread { show(0) }
            } catch (e: Exception) {
                ui("Kod kabul edilmedi: ${e.message}", cRed)
            }
        }
    }

    private fun connectClicked() {
        val h = ipBox.text.toString().trim()
        if (h.isEmpty()) {
            ui("Önce TV'nin IP adresini yaz", cRed)
            return
        }
        host = h
        ui("Bağlanıyor…", cAccent)
        fastIo.execute {
            try {
                connectRemote()
                runOnUiThread { show(0) }
            } catch (e: Exception) {
                ui("Bağlanamadı: ${e.message}", cRed)
            }
        }
    }

    @Synchronized
    private fun connectRemote() {
        ready = false
        remote?.close()
        val c = openTls(host, 6466, identity(), 0)
        remote = c
        Thread { readerLoop(c) }.apply { isDaemon = true }.start()
        waitReady()
    }

    private fun waitReady() {
        var waited = 0
        while (!ready && waited < 2500) {
            Thread.sleep(25)
            waited += 25
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
                            ui("Bağlandı", cGreen)
                        }
                    }
                }
            }
        } catch (_: Exception) {
            if (remote === c) {
                remote = null
                ready = false
                ui("Bağlantı koptu", cRed)
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
        if (host.isEmpty()) throw IllegalStateException("TV IP girilmemiş")
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
        remote!!.send(msg)
    }

    private fun sendKey(code: Int) = fastIo.execute {
        try {
            writeKey(code)
        } catch (e: Exception) {
            ui("Gönderilemedi: ${e.message}", cRed)
        }
    }

    private fun sendText(t: String) {
        if (t.isEmpty()) return
        fastIo.execute {
            try {
                for (ch in t.lowercase()) {
                    val code = when (ch) {
                        in 'a'..'z' -> 29 + (ch - 'a')
                        in '0'..'9' -> 7 + (ch - '0')
                        ' ' -> 62
                        '.' -> 56
                        ',' -> 55
                        '-' -> 69
                        else -> -1
                    }
                    if (code >= 0) {
                        writeKey(code)
                        Thread.sleep(15)
                    }
                }
            } catch (e: Exception) {
                ui("Gönderilemedi: ${e.message}", cRed)
            }
        }
    }
}
