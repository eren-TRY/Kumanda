package com.example.tvkumanda

import android.app.Activity
import android.os.Bundle
import android.view.View
import android.widget.Button
import android.widget.EditText
import android.widget.LinearLayout
import android.widget.ScrollView
import android.widget.TextView
import dadb.AdbKeyPair
import dadb.Dadb
import java.io.File
import java.util.concurrent.Executors

class MainActivity : Activity() {

    private val io = Executors.newSingleThreadExecutor()
    private var adb: Dadb? = null
    private lateinit var status: TextView
    private lateinit var ipBox: EditText
    private lateinit var textBox: EditText
    private var dp = 1f

    private fun px(v: Int) = (v * dp).toInt()

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        dp = resources.displayMetrics.density
        val prefs = getSharedPreferences("tv", MODE_PRIVATE)

        val root = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setPadding(px(16), px(32), px(16), px(24))
        }

        // Baglanti
        ipBox = EditText(this).apply {
            hint = "TV IP (örn. 192.168.1.50)"
            setText(prefs.getString("ip", ""))
            setSingleLine()
        }
        root.addView(ipBox)

        val connectBtn = Button(this).apply {
            text = "Bağlan"
            setOnClickListener {
                prefs.edit().putString("ip", ipBox.text.toString().trim()).apply()
                connect()
            }
        }
        root.addView(connectBtn)

        status = TextView(this).apply {
            text = "Bağlı değil"
            setPadding(0, px(8), 0, px(16))
        }
        root.addView(status)

        // Yon tuslari
        root.addView(row(gap(), key("▲", 19), gap()))
        root.addView(row(key("◀", 21), key("OK", 23), key("▶", 22)))
        root.addView(row(gap(), key("▼", 20), gap()))

        // Geri / Ana ekran / Menu
        root.addView(row(key("Geri", 4), key("Ana", 3), key("Menü", 82)))

        // Ses / guc
        root.addView(row(key("Ses -", 25), key("Sessiz", 164), key("Ses +", 24)))
        root.addView(row(key("Oynat/Dur", 85), key("Aç/Kapat", 26)))

        // Klavye
        textBox = EditText(this).apply {
            hint = "TV'ye yazılacak metin"
            setSingleLine()
        }
        root.addView(textBox)
        root.addView(Button(this).apply {
            text = "Yazıyı gönder"
            setOnClickListener { sendText(textBox.text.toString()) }
        })
        root.addView(row(key("Sil", 67), key("Enter", 66)))

        setContentView(ScrollView(this).apply { addView(root) })
    }

    private fun row(vararg views: View) = LinearLayout(this).apply {
        orientation = LinearLayout.HORIZONTAL
        views.forEach { addView(it) }
    }

    private fun key(label: String, code: Int) = Button(this).apply {
        text = label
        layoutParams = LinearLayout.LayoutParams(0, px(72), 1f)
        setOnClickListener { send("input keyevent $code") }
    }

    private fun gap() = View(this).apply {
        layoutParams = LinearLayout.LayoutParams(0, px(72), 1f)
    }

    private fun ui(s: String) = runOnUiThread { status.text = s }

    private fun connect() {
        val raw = ipBox.text.toString().trim()
        if (raw.isEmpty()) {
            status.text = "Önce TV'nin IP adresini yaz"
            return
        }
        status.text = "Bağlanıyor… TV'de izin penceresi çıkarsa 'Her zaman izin ver' de"
        io.execute {
            try {
                val host = raw.substringBefore(":")
                val port = raw.substringAfter(":", "5555").toInt()
                val priv = File(filesDir, "adbkey")
                val pub = File(filesDir, "adbkey.pub")
                if (!priv.exists() || !pub.exists()) AdbKeyPair.generate(priv, pub)
                val pair = AdbKeyPair.read(priv, pub)
                adb?.close()
                val d = Dadb.create(host, port, pair)
                d.shell("echo ok")
                adb = d
                ui("Bağlandı ✔")
            } catch (e: Exception) {
                adb = null
                ui("Bağlanamadı: ${e.message}")
            }
        }
    }

    private fun send(cmd: String) = io.execute {
        try {
            val d = adb ?: throw IllegalStateException("Önce bağlan")
            d.shell(cmd)
        } catch (e: Exception) {
            adb = null
            ui("Hata: ${e.message}")
        }
    }

    private fun sendText(t: String) {
        if (t.isEmpty()) return
        val special = "\\'\"&|;<>()$`*?[]{}~!#^"
        val esc = StringBuilder()
        for (c in t) {
            when {
                c == ' ' -> esc.append("%s")
                special.indexOf(c) >= 0 -> esc.append('\\').append(c)
                else -> esc.append(c)
            }
        }
        send("input text $esc")
    }
}
