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
import dadb.AdbKeyPair
import dadb.AdbShellPacket
import dadb.AdbShellStream
import dadb.Dadb
import java.io.File
import java.util.concurrent.Executors
import kotlin.math.abs

class MainActivity : Activity() {

    private val io = Executors.newSingleThreadExecutor()
    private var adb: Dadb? = null
    private var shell: AdbShellStream? = null
    private lateinit var status: TextView
    private lateinit var ipBox: EditText
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

        // Baglanti satiri
        ipBox = EditText(this).apply {
            hint = "TV IP"
            setHintTextColor(Color.GRAY)
            setTextColor(Color.WHITE)
            setText(prefs.getString("ip", ""))
            setSingleLine()
            layoutParams = LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f)
        }
        val connectBtn = Button(this).apply {
            text = "Bağlan"
            style(this, cAccent)
            setOnClickListener {
                prefs.edit().putString("ip", ipBox.text.toString().trim()).apply()
                connect()
            }
        }
        root.addView(LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER_VERTICAL
            addView(ipBox)
            addView(connectBtn)
        })

        status = TextView(this).apply {
            text = "Bağlı değil"
            setTextColor(Color.LTGRAY)
            setPadding(px(4), px(4), 0, px(12))
        }
        root.addView(status)

        // Yon tuslari
        root.addView(row(gap(), key("▲", 19), gap()))
        root.addView(row(key("◀", 21), key("OK", 23, cAccent), key("▶", 22)))
        root.addView(row(gap(), key("▼", 20), gap()))

        // Dokunmatik alan
        root.addView(touchPad())

        // Geri / Ana / Ayarlar
        root.addView(row(key("Geri", 4), key("Ana", 3), cmd("Ayarlar", "am start -a android.settings.SETTINGS")))

        // Ses
        root.addView(row(key("Ses −", 25), key("Sessiz", 164), key("Ses +", 24)))
        root.addView(row(key("⏯", 85), key("Aç/
