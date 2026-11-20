package com.example.tvkumanda

import android.annotation.SuppressLint
import android.app.Activity
import android.graphics.Color
import android.graphics.drawable.GradientDrawable
import android.os.Bundle
import android.view.Gravity
import android.view.MotionEvent
import android.view.View
import android.widget.Button
import android.widget.EditText
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
import kotlin.math.abs

// ---------------- Protobuf (elle, bagimlilik yok) ----------------

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

// ---------------- TLS yardimcilari ----------------

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

// ---------------- Uygulama ----------------

class MainActivity : Activity() {

    private val io = Executors.newSingleThreadExecutor()
    private var identity: Identity? = null
    private var remote: Conn? = null
    @Volatile private var ready = false
    private var pairConn: Conn? = null
    private var pairServerCert: X509Certificate? = null
    private var host = ""

    private lateinit var status: TextView
    private lateinit var ipBox: EditText
    private lateinit var codeBox: EditText
    private lateinit var codeRow: LinearLayout
    private lateinit var textBox: EditText
    private var dp = 1f

    private val cBg = Color.parseColor("#121214")
    private val cBtn = Color.parseColor("#2A2B30")
    private val cAccent = Color.parseColor("#3D7BFF")
    private val cRed = Color.parseColor("#D9363E")

    private fun px(v: Int) = (v * dp).toInt()

    @SuppressLint("ClickableViewAccessibility")
    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        dp = resources.displayMetrics.density
        val prefs = getSharedPreferences("tv", MODE_PRIVATE)

        val root = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setBackgroundColor(cBg)
            setPadding(px(14), px(30), px(14), px(24))
        }

        ipBox = EditText(this).apply {
            hint = "TV IP (örn. 192.168.1.105)"
            setHintTextColor(Color.GRAY)
            setTextColor(Color.WHITE)
            setText(prefs.getString("ip", ""))
            setSingleLine()
        }
        root.addView(ipBox)

        root.addView(row(
            Button(this).apply {
                text = "Eşleştir"
                style(this, cBtn)
                layoutParams = lp(52)
                setOnClickListener {
                    prefs.edit().putString("ip", ipBox.text.toString().trim()).apply()
                    startPairing()
                }
            },
            Button(this).apply {
                text = "Bağlan"
                style(this, cAccent)
                layoutParams = lp(52)
                setOnClickListener {
                    prefs.edit().putString("ip", ipBox.text.toString().trim()).apply()
                    connectClicked()
                }
            }
        ))

        codeBox = EditText(this).apply {
            hint = "TV'deki 6 haneli kod"
            setHintTextColor(Color.GRAY)
            setTextColor(Color.WHITE)
            setSingleLine()
            layoutParams = LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f)
        }
        codeRow = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER_VERTICAL
            visibility = View.GONE
            addView(codeBox)
            addView(Button(this@MainActivity).apply {
                text = "Onayla"
                style(this, cAccent)
                setOnClickListener { finishPairing(codeBox.text.toString()) }
            })
        }
        root.addView(codeRow)

        status = TextView(this).apply {
            text = if (prefs.getBoolean("paired", false)) "Bağlı değil" else "Önce Eşleştir'e bas"
            setTextColor(Color.LTGRAY)
            setPadding(px(4), px(8), 0, px(12))
        }
        root.addView(status)

        root.addView(row(gap(), key("▲", 19), gap()))
        root.addView(row(key("◀", 21), key("OK", 23, cAccent), key("▶", 22)))
        root.addView(row(gap(), key("▼", 20), gap()))

        root.addView(touchPad())

        root.addView(row(key("Geri", 4), key("Ana", 3), key("Ayarlar", 176)))
        root.addView(row(key("Ses −", 25), key("Sessiz", 164), key("Ses +", 24)))
        root.addView(row(key("⏯", 85), key("Aç/Kapat", 26, cRed)))

        textBox = EditText(this).apply {
            hint = "TV'ye yazılacak metin (a-z, 0-9)"
            setHintTextColor(Color.GRAY)
            setTextColor(Color.WHITE)
            setSingleLine()
        }
        root.addView(textBox)
        root.addView(row(
            Button(this).apply {
                text = "Gönder"
                style(this, cAccent)
                layoutParams = lp()
                setOnClickListener { sendText(textBox.text.toString()) }
            },
            key("Sil", 67),
            key("Enter", 66)
        ))

        setContentView(ScrollView(this).apply {
            setBackgroundColor(cBg)
            addView(root)
        })

        if (prefs.getBoolean("paired", false) && ipBox.text.isNotBlank()) connectClicked()
    }

    // ---------- UI yardimcilari ----------

    private fun lp(h: Int = 68) = LinearLayout.LayoutParams(0, px(h), 1f).apply {
        setMargins(px(4), px(4), px(4), px(4))
    }

    private fun style(b: Button, color: Int) {
        b.background = GradientDrawable().apply {
            cornerRadius = px(16).toFloat()
            setColor(color)
        }
        b.setTextColor(Color.WHITE)
        b.isAllCaps = false
        b.textSize = 16f
    }

    private fun row(vararg views: View) = LinearLayout(this).apply {
        orientation = LinearLayout.HORIZONTAL
        views.forEach { addView(it) }
    }

    private fun key(label: String, code: Int, color: Int = cBtn) = Button(this).apply {
        text = label
        style(this, color)
        layoutParams = lp()
        setOnClickListener { sendKey(code) }
    }

    private fun gap() = View(this).apply { layoutParams = lp() }

    @SuppressLint("ClickableViewAccessibility")
    private fun touchPad() = TextView(this).apply {
        text = "Dokunmatik alan\nkaydır = yön, dokun = OK"
        setTextColor(Color.GRAY)
        gravity = Gravity.CENTER
        background = GradientDrawable().apply {
            cornerRadius = px(20).toFloat()
            setColor(Color.parseColor("#1D1E22"))
        }
        layoutParams = LinearLayout.LayoutParams(
            LinearLayout.LayoutParams.MATCH_PARENT, px(200)
        ).apply { setMargins(px(4), px(10), px(4), px(10)) }

        var lastX = 0f
        var lastY = 0f
        var moved = false
        val step = px(48).toFloat()

        setOnTouchListener { v, e ->
            when (e.action) {
                MotionEvent.ACTION_DOWN -> {
                    v.parent.requestDisallowInterceptTouchEvent(true)
                    lastX = e.x; lastY = e.y; moved = false
                }
                MotionEvent.ACTION_MOVE -> {
                    val dx = e.x - lastX
                    val dy = e.y - lastY
                    if (abs(dx) > step || abs(dy) > step) {
                        val code = if (abs(dx) > abs(dy)) {
                            if (dx > 0) 22 else 21
                        } else {
                            if (dy > 0) 20 else 19
                        }
                        sendKey(code)
                        moved = true
                        lastX = e.x; lastY = e.y
                    }
                }
                MotionEvent.ACTION_UP -> if (!moved) sendKey(23)
            }
            true
        }
    }

    private fun ui(s: String) = runOnUiThread { status.text = s }

    // ---------- Kimlik (istemci sertifikasi) ----------

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
        s.connect(InetSocketAddress(h, port), 6000)
        s.tcpNoDelay = true
        s.soTimeout = readTimeoutMs
        s.startHandshake()
        return Conn(s)
    }

    // ---------- Eslestirme (port 6467) ----------

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
            status.text = "Önce TV'nin IP adresini yaz"
            return
        }
        host = h
        status.text = "Eşleştirme başlıyor…"
        io.execute {
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
                ui("TV'de çıkan 6 haneli kodu yazıp Onayla'ya bas")
            } catch (e: Exception) {
                ui("Eşleştirme başarısız: ${e.message}")
            }
        }
    }

    private fun finishPairing(raw: String) {
        val code = raw.trim().uppercase()
        if (code.length != 6) {
            status.text = "Kod 6 karakter olmalı"
            return
        }
        io.execute {
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
                ui("Eşleşti ✔ Bağlanıyor…")
                connectRemote()
            } catch (e: Exception) {
                ui("Kod kabul edilmedi: ${e.message}. Eşleştir'e basıp tekrar dene")
            }
        }
    }

    // ---------- Kumanda baglantisi (port 6466) ----------

    private fun connectClicked() {
        val h = ipBox.text.toString().trim()
        if (h.isEmpty()) {
            status.text = "Önce TV'nin IP adresini yaz"
            return
        }
        host = h
        status.text = "Bağlanıyor…"
        io.execute {
            try {
                connectRemote()
            } catch (e: Exception) {
                ui("Bağlanamadı: ${e.message}. Gerekirse Eşleştir'e bas")
            }
        }
    }

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
        while (!ready && waited < 4000) {
            Thread.sleep(100)
            waited += 100
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
                            ui("Bağlandı ✔")
                        }
                    }
                }
            }
        } catch (e: Exception) {
            if (remote === c) {
                remote = null
                ready = false
                ui("Bağlantı koptu (tuşa basınca otomatik yeniden bağlanır)")
            }
        }
    }

    private fun keyMsg(code: Int) = Pb.bytes(10, Pb.int(1, code) + Pb.int(2, 3))

    private fun writeKey(code: Int) {
        val msg = keyMsg(code)
        try {
            val c = remote ?: throw IllegalStateException("kapalı")
            c.send(msg)
        } catch (e: Exception) {
            if (host.isEmpty()) throw e
            connectRemote()
            remote!!.send(msg)
        }
    }

    private fun sendKey(code: Int) = io.execute {
        try {
            writeKey(code)
        } catch (e: Exception) {
            ui("Gönderilemedi: ${e.message}")
        }
    }

    private fun sendText(t: String) {
        if (t.isEmpty()) return
        io.execute {
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
                        Thread.sleep(40)
                    }
                }
            } catch (e: Exception) {
                ui("Gönderilemedi: ${e.message}")
            }
        }
    }
}
