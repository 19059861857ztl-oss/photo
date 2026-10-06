/* =========================================================================
 * 原图无损 P2P 传输 · 纯前端（无后端 / 无中转）
 * 信令：公共 MQTT over WebSocket（只交换 SDP + ICE，几百字节）
 * 数据：WebRTC DataChannel 点对点直传原始字节 → 不压缩、EXIF 完整保留
 * 兼容：iOS 15 Safari / Android / Windows / HarmonyOS 主流浏览器
 * ========================================================================= */
(function () {
  'use strict';

  /* ============================ 常量与工具 ============================ */
  var CHUNK = 16 * 1024;              // 每片 16KB：SCTP 跨浏览器最稳
  var HIGH = 1024 * 1024;             // 发送缓冲上限 1MB，超出等待排空
  var ICE = { iceServers: [{ urls: ['stun:stun.l.google.com:19302', 'stun:stun1.l.google.com:19302'] }] };
  var BROKERS = [                     // 公共信令，失败自动切换下一个
    'wss://broker.emqx.io:8084/mqtt',
    'wss://broker.hivemq.com:8884/mqtt'
  ];
  var TOPIC = function (r) { return 'lpt/v3/' + r; };
  var SALT = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';

  var $ = function (s) { return document.querySelector(s); };
  var uid = function () { return Math.random().toString(36).slice(2, 10) + Date.now().toString(36); };
  var randRoom = function () { var s = '', i; for (i = 0; i < 6; i++) s += SALT[Math.floor(Math.random() * SALT.length)]; return s; };
  var fmt = function (n) {
    return n < 1024 ? n + ' B' : n < 1048576 ? (n / 1024).toFixed(1) + ' KB' : (n / 1048576).toFixed(2) + ' MB';
  };
  var esc = function (s) { return String(s).replace(/[&<>"]/g, function (c) { return ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' })[c]; }); };

  function toast(msg, kind, ms) {
    var t = document.createElement('div');
    t.className = 'toast ' + (kind || '');
    t.textContent = msg;
    $('#toasts').appendChild(t);
    setTimeout(function () { if (t.parentNode) t.parentNode.removeChild(t); }, ms || 2600);
  }
  function status(text, cls) { var p = $('#status'); p.textContent = text; p.className = 'pill ' + (cls || ''); }

  /* 读取文件为 ArrayBuffer：FileReader 全平台兼容，Safari 15 优先 arrayBuffer() */
  function readFile(file) {
    return new Promise(function (res, rej) {
      if (file.arrayBuffer) { file.arrayBuffer().then(res, rej); return; }
      var fr = new FileReader();
      fr.onload = function () { res(fr.result); };
      fr.onerror = function () { rej(fr.error || new Error('读取失败')); };
      fr.readAsArrayBuffer(file);
    });
  }

  /* 检查 JPEG 前 256KB 是否含 EXIF（用于界面标注，不改动任何字节） */
  function hasExif(buf) {
    var n = Math.min(buf.byteLength, 262144), u = new Uint8Array(buf, 0, n), i, m = 0;
    var sig = [0x45, 0x78, 0x69, 0x66, 0x00, 0x00];  // "Exif\0\0"
    for (i = 0; i < n; i++) {
      if (u[i] === sig[m]) { m++; if (m === sig.length) return true; } else { m = u[i] === sig[0] ? 1 : 0; }
    }
    return false;
  }

  /* ============================ 界面元素 ============================ */
  var E = {
    qr: $('#qrbox'), room: $('#room'), gen: $('#gen'), scan: $('#scan'), join: $('#join'), copy: $('#copy'),
    drop: $('#drop'), file: $('#file'), queue: $('#queue'), send: $('#send'), clear: $('#clear'),
    bar: $('#bar'), pname: $('#pname'), pct: $('#pct'), speed: $('#speed'), eta: $('#eta'), retry: $('#retry'),
    recv: $('#recv'), recvbar: $('#recvbar'), saveall: $('#saveall'),
    mask: $('#scanmask'), video: $('#video'), scanclose: $('#scanclose')
  };

  /* ========== 液态玻璃按钮引擎（照搬鸿蒙 GlassButton 的交互模型） ==========
     DOM：.jelly 玻璃面（局部形变只作用于这一层，圆角硬裁剪）
            内含 .jglow 内跟随光晕 / .jripple 涟漪 / .jpart 微光粒子 / .jline 顶部高光
          .lbl 文字层：独立渲染，永不参与形变
     交互：按住 → 光晕(直径3×按钮高) + 涟漪(直径=触点到最远角×2) 自触点展开(480ms EaseOut)
           滑动 → 两者实时跟随手指；玻璃面以触点为原点做极小局部挤压(最大 2.5%)，260ms 阻尼跟随
           松手 → 光晕/涟漪 620ms 放大淡出；玻璃面 760ms 临界阻尼回位（无过冲，厚重）
           整体按钮 180ms 下沉 0.972 / hover 抬起 1.02
     ======================================================================== */
  var REDUCE = !!(window.matchMedia && window.matchMedia('(prefers-reduced-motion: reduce)').matches);
  var clamp = function (v, a, b) { return v < a ? a : v > b ? b : v; };
  var r2 = function (n) { return Math.round(n * 100) / 100; };
  var live = {};                                   // pointerId -> J

  /* 组装玻璃面与内部光效图层（只做一次） */
  function jellyify(el) {
    if (el.__j) return el.__j;
    var shell = document.createElement('i'); shell.className = 'jelly';
    var glow = document.createElement('i'); glow.className = 'jglow';    // 内跟随光晕
    var rip = document.createElement('i'); rip.className = 'jripple';    // 涟漪
    var pa = document.createElement('i'); pa.className = 'jpart a';      // 微光粒子
    var pb = document.createElement('i'); pb.className = 'jpart b';
    var line = document.createElement('i'); line.className = 'jline';    // 顶部高光扫边
    shell.appendChild(glow); shell.appendChild(rip);
    shell.appendChild(pa); shell.appendChild(pb); shell.appendChild(line);
    var lbl = document.createElement('span'); lbl.className = 'lbl';
    Array.prototype.slice.call(el.childNodes).forEach(function (n) {
      if (n.nodeType === 1 && n.tagName === 'INPUT') return;   // 表单控件留在原处
      lbl.appendChild(n);
    });
    el.insertBefore(shell, el.firstChild);
    el.appendChild(lbl);
    return (el.__j = {
      el: el, shell: shell, glow: glow, rip: rip, lbl: lbl,
      w: 1, h: 1, left: 0, top: 0, hot: false,
      px: 0, py: 0,                            // 当前触点（按钮内坐标）
      sx: 1, sy: 1, tx: 1, ty: 1,              // 玻璃面局部挤压：当前值 / 目标值
      gS: 0.72, gA: 0, gS0: 0.72, gA0: 0, gSt: 1, gAt: 1, gT: 0, gD: 480,
      rS: 0.32, rA: 0, rS0: 0.32, rA0: 0, rSt: 1, rAt: 1, rT: 0, rD: 480,
      gSize: 0, rSize: 0, raf: 0, t: 0
    });
  }

  /* 补间：easeOutCubic（对应参考实现的 480 / 620ms EaseOut） */
  function setTween(J, w, ts, ta, dur, now) {
    if (w === 'g') {
      J.gS0 = J.gS; J.gA0 = J.gA; J.gSt = ts; J.gAt = ta; J.gD = dur; J.gT = now;
    } else {
      J.rS0 = J.rS; J.rA0 = J.rA; J.rSt = ts; J.rAt = ta; J.rD = dur; J.rT = now;
    }
  }
  function tween(J, w, now) {
    var d = (w === 'g' ? J.gD : J.rD), t0 = (w === 'g' ? J.gT : J.rT);
    var u = d > 0 ? clamp((now - t0) / d, 0, 1) : 1;
    var e = 1 - Math.pow(1 - u, 3);
    if (w === 'g') {
      J.gS = J.gS0 + (J.gSt - J.gS0) * e;
      J.gA = J.gA0 + (J.gAt - J.gA0) * e;
    } else {
      J.rS = J.rS0 + (J.rSt - J.rS0) * e;
      J.rA = J.rA0 + (J.rAt - J.rA0) * e;
    }
    return u < 1;
  }

  /* 量取几何：.btn 自身不变形，取到的是布局矩形（稳定） */
  function measure(J) {
    var r = J.el.getBoundingClientRect();
    J.left = r.left; J.top = r.top; J.w = r.width || 1; J.h = r.height || 1;
  }

  /* 局部厚重挤压：变换原点 = 触点；越靠边压缩越明显（最大 2.5%），只作用于玻璃面 */
  function deform(J, x, y) {
    var cx = clamp(x, 0, J.w), cy = clamp(y, 0, J.h);
    J.px = x; J.py = y;
    var ox = Math.abs(cx / J.w - 0.5) * 2;        // 0 = 水平居中，1 = 贴左右边
    var oy = Math.abs(cy / J.h - 0.5) * 2;        // 0 = 垂直居中，1 = 贴上下边
    J.shell.style.transformOrigin = r2(cx) + 'px ' + r2(cy) + 'px';
    J.tx = 1 - 0.025 * oy;
    J.ty = 1 - 0.025 * ox;
  }

  function Jstart(J, e) {
    measure(J);
    J.el.classList.add('press');
    J.hot = true;
    var x = clamp(e.clientX - J.left, 0, J.w), y = clamp(e.clientY - J.top, 0, J.h);
    // ① 跟随光晕：直径 = 3.6 × 按钮高度（内发光，超出圆角部分被裁掉）
    J.gSize = Math.max(56, J.h * 3.6);
    J.glow.style.width = J.gSize + 'px'; J.glow.style.height = J.gSize + 'px';
    // ② 涟漪：直径 = 触点到最远角距离 × 2，保证能铺满整个按钮
    var dx = Math.max(x, J.w - x), dy = Math.max(y, J.h - y);
    J.rSize = 2 * Math.sqrt(dx * dx + dy * dy);
    J.rip.style.width = J.rSize + 'px'; J.rip.style.height = J.rSize + 'px';
    var now = performance.now();
    setTween(J, 'g', 1, 1, 480, now);
    setTween(J, 'r', 1, 1, 480, now);
    deform(J, x, y);
    J.sx = J.tx; J.sy = J.ty;                 // 按下瞬间立即成型（不延迟）
    paint(J); run(J);
  }
  function Jmove(J, e) {
    if (J.hot) deform(J, clamp(e.clientX - J.left, 0, J.w), clamp(e.clientY - J.top, 0, J.h));
  }
  function Jend(J) {
    J.hot = false;
    J.el.classList.remove('press');
    var now = performance.now();
    setTween(J, 'g', 1.12, 0, 620, now);       // 光晕：放大同时淡出
    setTween(J, 'r', 1.16, 0, 620, now);       // 涟漪：扩散同时淡出
    J.tx = 1; J.ty = 1;                        // 760ms 临界阻尼回位（无过冲，厚重沉稳）
    run(J);
  }

  function run(J) {
    if (J.raf || REDUCE) return;
    J.t = performance.now();
    J.raf = requestAnimationFrame(function loop(now) {
      var dt = clamp((now - J.t) / 1000, 0.001, 0.034); J.t = now;
      if (tick(J, now, dt)) J.raf = requestAnimationFrame(loop);
      else J.raf = 0;
    });
  }

  function tick(J, now, dt) {
    // 按住：约 100ms 阻尼跟随（慢半拍 = 厚重）；松手：约 210ms 时间常数 ≈ 760ms 落定且无过冲
    var tau = J.hot ? 0.10 : 0.21;
    var e = 1 - Math.exp(-dt / tau);
    J.sx += (J.tx - J.sx) * e;
    J.sy += (J.ty - J.sy) * e;
    var moving = Math.abs(J.sx - J.tx) > 0.00015 || Math.abs(J.sy - J.ty) > 0.00015;
    var g = tween(J, 'g', now), r = tween(J, 'r', now);
    paint(J);
    return J.hot || moving || g || r;
  }

  function paint(J) {
    // 玻璃面局部挤压（文字层不参与 → 字形永不被扭曲）
    J.shell.style.transform = 'scale(' + r2(J.sx) + ',' + r2(J.sy) + ')';
    // 光晕 / 涟漪：圆心 = 触点，按住滑动时实时跟随手指，且被玻璃面圆角硬裁剪
    J.glow.style.transform = 'translate3d(' + r2(J.px - J.gSize / 2) + 'px,' +
      r2(J.py - J.gSize / 2) + 'px,0) scale(' + r2(J.gS) + ')';
    J.glow.style.opacity = r2(J.gA);
    J.rip.style.transform = 'translate3d(' + r2(J.px - J.rSize / 2) + 'px,' +
      r2(J.py - J.rSize / 2) + 'px,0) scale(' + r2(J.rS) + ')';
    J.rip.style.opacity = r2(J.rA);
  }

  function targetOf(t) {
    if (!t || !t.closest) return null;
    var b = t.closest('.btn,.drop');
    if (!b || b.disabled) return null;
    return jellyify(b, b.classList.contains('drop') ? 0.75 : 1);
  }

  if (REDUCE) {
    // 「减弱动态效果」：不做跟手形变，但保留按压下沉反馈（不静默失效）
    document.addEventListener('pointerdown', function (e) {
      var J = targetOf(e.target); if (!J) return;
      live[e.pointerId] = J; J.el.classList.add('jr');
    }, { passive: true });
    ['pointerup', 'pointercancel'].forEach(function (ev) {
      document.addEventListener(ev, function (e) {
        var J = live[e.pointerId]; if (!J) return;
        delete live[e.pointerId]; J.el.classList.remove('jr');
      }, true);
    });
  } else {
    document.addEventListener('pointerdown', function (e) {
      var J = targetOf(e.target); if (!J) return;
      live[e.pointerId] = J; Jstart(J, e);
    }, { passive: true });
    document.addEventListener('pointermove', function (e) {
      var J = live[e.pointerId];
      if (J) Jmove(J, e);                                  // 按住滑动：光效与形变实时跟手
    }, { passive: true });
    ['pointerup', 'pointercancel'].forEach(function (ev) {
      document.addEventListener(ev, function (e) {
        var J = live[e.pointerId]; if (!J) return;
        delete live[e.pointerId]; Jend(J);
      }, true);
    });
    // 桌面端 hover：整体抬起 1.02，玻璃描边/阴影由 CSS 平滑过渡
    var hov = null;
    var setHov = function (H) {
      if (hov === H) return;
      if (hov) hov.el.classList.remove('over');
      hov = H;
      if (hov) hov.el.classList.add('over');
    };
    document.addEventListener('pointerover', function (e) {
      if (e.pointerType !== 'mouse') return;
      var b = (e.target && e.target.closest) ? e.target.closest('.btn,.drop') : null;
      setHov((b && !b.disabled) ? jellyify(b) : null);
    }, { passive: true });
    document.addEventListener('mouseleave', function () { setHov(null); });
  }
  // 静态按钮先建好玻璃面与光效层，保证首屏就有质感
  Array.prototype.forEach.call(document.querySelectorAll('.btn,.drop'), function (b) { jellyify(b); });

  /* ============================ 状态 ============================ */
  var role = '';            // host（生成二维码方）| guest（扫码方）
  var room = '';
  var myId = uid();
  var pc = null, dc = null;
  var pendingCand = [];
  var retries = 0, retryTimer = null;
  var queue = [];           // 待发送：{file, url, el}
  var rx = null;            // 接收中：{meta, chunks, size, t0}
  var sending = false;
  var acks = {};
  var scanRaf = 0, scanStream = null;

  /* ============================ 信令（仅交换连接信息） ============================ */
  var sig = {
    c: null, ready: false, everOk: false, bi: 0, room: '',
    open: function (rm, onReady) {
      if (typeof mqtt === 'undefined') { toast('信令库未加载，请检查网络后刷新', 'bad', 4200); return; }
      sig.room = rm;
      (function tryBroker(i) {
        if (i >= BROKERS.length) { toast('信令服务器连接失败，请检查网络', 'bad', 4200); status('信令失败', 'bad'); return; }
        sig.bi = i;
        var c;
        try { c = mqtt.connect(BROKERS[i], { clientId: 'lpt_' + myId, clean: true, keepalive: 30, connectTimeout: 8000, reconnectPeriod: 5000 }); }
        catch (err) { tryBroker(i + 1); return; }
        sig.c = c;
        c.on('connect', function () {
          sig.everOk = true; sig.ready = true;
          c.subscribe(TOPIC(sig.room), { qos: 0 });
          if (onReady) onReady();
        });
        c.on('message', function (t, p) { sig.recv(p); });
        c.on('error', function () { if (!sig.everOk) { try { c.end(true); } catch (e) {} tryBroker(i + 1); } });
      })(0);
    },
    send: function (o) {
      if (!sig.c || !sig.ready) return;
      o.f = myId;
      try { sig.c.publish(TOPIC(sig.room), JSON.stringify(o), { qos: 0, retain: false }); } catch (e) {}
    },
    recv: function (payload) {
      var m;
      try { m = JSON.parse(payload.toString()); } catch (e) { return; }
      if (!m || m.f === myId) return;                    // 忽略自己发的
      try {
        if (m.t === 'offer') onOffer(m.sdp);
        else if (m.t === 'answer') onAnswer(m.sdp);
        else if (m.t === 'cand') addCand(m.c);
        else if (m.t === 'hello' && role === 'host') resendOffer();
      } catch (e) { /* 信令异常不致命 */ }
    }
  };

  /* ============================ WebRTC ============================ */
  function ensurePC() {
    if (pc) return pc;
    pc = new RTCPeerConnection(ICE);
    pc.onicecandidate = function (e) {
      if (e.candidate) sig.send({ t: 'cand', c: e.candidate.toJSON ? e.candidate.toJSON() : e.candidate });
    };
    pc.oniceconnectionstatechange = onIceState;
    if (role === 'guest') pc.ondatachannel = function (e) { bindDC(e.channel); };
    return pc;
  }

  function bindDC(ch) {
    dc = ch;
    try { dc.binaryType = 'arraybuffer'; } catch (e) {}
    dc.bufferedAmountLowThreshold = 256 * 1024;
    dc.onopen = function () {
      retries = 0;
      status('已连接 · P2P 直传', 'ok');
      updateSendBtn();
      toast('P2P 连接已建立', 'ok');
    };
    dc.onclose = function () { status('连接已断开', 'bad'); updateSendBtn(); };
    dc.onmessage = onData;
  }

  function onIceState() {
    if (!pc) return;
    var s = pc.iceConnectionState;
    if (s === 'connected' || s === 'completed') { retries = 0; status('已连接 · P2P 直传', 'ok'); }
    else if (s === 'checking') status('连接中…', 'warn');
    else if (s === 'disconnected') status('网络抖动，等待恢复…', 'warn');
    else if (s === 'failed') { status('连接中断，自动重连…', 'bad'); scheduleRetry(); }
  }

  function scheduleRetry() {
    if (retryTimer || retries >= 5) return;
    retries++;
    retryTimer = setTimeout(function () {
      retryTimer = null;
      status('重连中（第 ' + retries + ' 次）…', 'warn');
      iceRestart();
    }, 1200 * retries);
  }

  function iceRestart() {
    if (!pc) { toast('连接已释放，请重新配对', 'warn'); return; }
    if (role === 'host') {
      pc.createOffer({ iceRestart: true }).then(function (o) {
        return pc.setLocalDescription(o);
      }).then(function () {
        sig.send({ t: 'offer', sdp: pc.localDescription });
      }).catch(function () { toast('重连失败，请点「重连 / 重试」', 'bad'); });
    } else {
      sig.send({ t: 'hello' });         // 客机请求主机重新发 offer
    }
  }

  function addCand(c) {
    if (!c) return;
    if (!pc || !pc.remoteDescription) { pendingCand.push(c); return; }
    try { pc.addIceCandidate(new RTCIceCandidate(c)).catch(function () {}); } catch (e) {}
  }
  function flushCand() {
    pendingCand.forEach(function (c) { addCand(c); });
    pendingCand = [];
  }

  function resendOffer() {
    if (role !== 'host' || !pc || !pc.localDescription) return;
    if (dc && dc.readyState === 'open') return;
    sig.send({ t: 'offer', sdp: pc.localDescription });
  }

  function onOffer(sdp) {
    if (!pc) ensurePC();
    var set = function () { return pc.setRemoteDescription(new RTCSessionDescription(sdp)); };
    set().catch(function () {                       // 状态冲突时重建连接对象
      try { pc.close(); } catch (e) {}
      pc = null; dc = null; ensurePC();
      return pc.setRemoteDescription(new RTCSessionDescription(sdp));
    }).then(function () {
      flushCand();
      return pc.createAnswer();
    }).then(function (a) {
      return pc.setLocalDescription(a);
    }).then(function () {
      sig.send({ t: 'answer', sdp: pc.localDescription });
      status('正在建立 P2P…', 'warn');
    }).catch(function () { toast('应答失败，请重新扫码', 'bad'); });
  }

  function onAnswer(sdp) {
    if (!pc || pc.signalingState !== 'have-local-offer') return;
    pc.setRemoteDescription(new RTCSessionDescription(sdp)).then(function () {
      flushCand();
      status('正在建立 P2P…', 'warn');
    }).catch(function () {});
  }

  /* ============================ 建立配对 ============================ */
  function startHost(rm) {
    role = 'host'; room = rm; E.room.value = rm;
    status('等待对方扫码…', 'warn');
    drawQR(rm);
    sig.open(rm, function () {
      ensurePC();
      if (!dc) bindDC(pc.createDataChannel('img', { ordered: true }));
      pc.createOffer().then(function (o) { return pc.setLocalDescription(o); }).then(function () {
        sig.send({ t: 'offer', sdp: pc.localDescription });
      }).catch(function () { toast('创建连接失败，请重试', 'bad'); });
    });
  }

  function startGuest(rm) {
    role = 'guest'; room = rm; E.room.value = rm;
    status('正在加入房间…', 'warn');
    sig.open(rm, function () {
      sig.send({ t: 'hello' });
      status('已入房，等待主机应答…', 'warn');
      setTimeout(function () { if (role === 'guest') sig.send({ t: 'hello' }); }, 2500);
    });
  }

  /* ============================ 二维码 / 扫码 ============================ */
  function drawQR(rm) {
    var link = location.protocol === 'file:'
      ? rm
      : location.origin + location.pathname + '?r=' + encodeURIComponent(rm);
    try {
      var qr = qrcode(0, 'M');
      qr.addData(link); qr.make();
      E.qr.className = 'qrbox filled';
      E.qr.innerHTML = qr.createSvgTag({ cellSize: 4, margin: 1, scalable: true });
    } catch (e) {
      E.qr.className = 'qrbox filled';
      E.qr.innerHTML = '<div class="qrph"><b style="font-size:30px;letter-spacing:4px">' + esc(rm) + '</b><span>二维码库未加载，请对方手动输入此房间号</span></div>';
    }
  }

  function openScan() {
    if (!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia) {
      toast('当前环境不支持摄像头（需 HTTPS 访问）', 'bad', 4000);
      return;
    }
    if (typeof jsQR === 'undefined') { toast('扫码库未加载，请改用手动输入房间号', 'warn', 4000); return; }
    navigator.mediaDevices.getUserMedia({
      video: { facingMode: { ideal: 'environment' }, width: { ideal: 1280 }, height: { ideal: 720 } },
      audio: false
    }).then(function (stream) {
      scanStream = stream;
      E.video.srcObject = stream;
      E.mask.classList.add('on');
      var p = E.video.play(); if (p && p.catch) p.catch(function () {});
      scanRaf = requestAnimationFrame(tick);
    }).catch(function (err) {
      toast('无法打开摄像头：' + (err && err.name ? err.name : '未知错误'), 'bad', 4000);
    });
  }

  var cv = document.createElement('canvas');
  var cx = cv.getContext('2d', { willReadFrequently: true });
  function tick() {
    if (!scanStream) return;
    if (E.video.readyState === E.video.HAVE_ENOUGH_DATA) {
      cv.width = E.video.videoWidth; cv.height = E.video.videoHeight;
      cx.drawImage(E.video, 0, 0, cv.width, cv.height);
      var img = cx.getImageData(0, 0, cv.width, cv.height);
      var code = jsQR(img.data, img.width, img.height, { inversionAttempts: 'dontInvert' });
      if (code && code.data) { onScanned(code.data); return; }
    }
    scanRaf = requestAnimationFrame(tick);
  }

  function closeScan() {
    if (scanRaf) cancelAnimationFrame(scanRaf), scanRaf = 0;
    if (scanStream) { scanStream.getTracks().forEach(function (t) { t.stop(); }); scanStream = null; }
    E.video.srcObject = null;
    E.mask.classList.remove('on');
  }

  function onScanned(text) {
    closeScan();
    var rm = parseRoom(text);
    if (!rm) { toast('二维码内容无法识别，请手动输入房间号', 'warn', 3600); return; }
    if (rm === room && (dc && dc.readyState === 'open')) { toast('已与该房间连接', 'ok'); return; }
    resetPeer();
    startGuest(rm);
    toast('已识别房间 ' + rm + '，正在连接…', 'ok');
  }

  /* 二维码内容：完整链接 / ?r=XXX / 纯房间号 都能解析 */
  function parseRoom(text) {
    var s = String(text).trim();
    try { var u = new URL(s); var r = u.searchParams.get('r'); if (r) return r.toUpperCase().slice(0, 12); } catch (e) {}
    var m = s.match(/[?&]r=([A-Za-z0-9_-]{3,12})/); if (m) return m[1].toUpperCase();
    m = s.match(/^[A-Za-z0-9_-]{3,12}$/); if (m) return s.toUpperCase();
    return '';
  }

  /* ============================ 传输协议 ============================ */
  /* 控制帧（字符串）：{t:'meta'|'end'|'ack', ...}；数据帧：ArrayBuffer 原始字节 */
  function onData(ev) {
    var d = ev.data;
    if (typeof d === 'string') { ctl(d); return; }
    if (!rx) return;
    // Safari/Chrome 指定 binaryType='arraybuffer'；极端情况兜底 Blob
    if (d instanceof ArrayBuffer) { push(new Uint8Array(d)); }
    else if (d && d.size !== undefined && typeof FileReader !== 'undefined') {
      var fr = new FileReader();
      fr.onload = function () { push(new Uint8Array(fr.result)); };
      fr.readAsArrayBuffer(d);
    }
  }

  function push(u8) {
    rx.chunks.push(u8); rx.got += u8.length;
    if (!rx.rxT0) rx.rxT0 = Date.now();
    progress(rx.got, rx.meta.size, '接收：' + rx.meta.name, rx.rxT0);
    if (rx.got >= rx.meta.size) finishRecv();
  }

  function ctl(str) {
    var m;
    try { m = JSON.parse(str); } catch (e) { return; }
    if (m.t === 'meta') {
      rx = { meta: m, chunks: [], got: 0, rxT0: 0 };
      progress(0, m.size, '接收：' + m.name, 0);
    } else if (m.t === 'end') {
      if (rx && rx.meta.id === m.id) finishRecv();   // 收到结束帧即落盘，不依赖字节数比对
      if (dc && dc.readyState === 'open') dc.send(JSON.stringify({ t: 'ack', id: m.id }));
    } else if (m.t === 'ack') {
      if (acks[m.id]) { acks[m.id](); delete acks[m.id]; }
    }
  }

  function finishRecv() {
    if (!rx) return;
    var meta = rx.meta, blob = new Blob(rx.chunks, { type: meta.mime || 'application/octet-stream' });
    rx = null;
    addRecv(meta, blob);
    setProgress(1, 1, '接收完成：' + meta.name, Date.now() - 1, true);
    toast('已收到原图：' + meta.name, 'ok', 3200);
    if (navigator.vibrate) navigator.vibrate(30);
  }

  function sendAll() {
    if (!dc || dc.readyState !== 'open') { toast('尚未连接，无法发送', 'warn'); return; }
    if (!queue.length) { toast('请先选择图片', 'warn'); return; }
    if (sending) return;
    sending = true; E.send.disabled = true;
    var i = 0;
    (function next() {
      if (i >= queue.length) {
        sending = false; updateSendBtn();
        setProgress(1, 1, '全部发送完成', Date.now() - 1, true);
        toast('全部原图已送达', 'ok', 3200);
        if (navigator.vibrate) navigator.vibrate([20, 40, 20]);
        return;
      }
      var it = queue[i++];
      sendOne(it).then(next, function (err) {
        sending = false; updateSendBtn();
        toast('发送中断：' + (err && err.message ? err.message : '连接异常'), 'bad', 4200);
      });
    })();
  }

  function sendOne(it) {
    return readFile(it.file).then(function (buf) {
      var id = uid();
      var meta = {
        t: 'meta', id: id, name: it.file.name || ('IMG_' + Date.now() + '.jpg'),
        size: buf.byteLength, mime: it.file.type || 'application/octet-stream',
        last: it.file.lastModified || Date.now()
      };
      dc.send(JSON.stringify(meta));
      var off = 0, t0 = Date.now();
      return new Promise(function (res, rej) {
        (function pump() {
          if (!dc || dc.readyState !== 'open') { rej(new Error('连接已断开（已发 ' + fmt(off) + '）')); return; }
          if (off >= buf.byteLength) {
            dc.send(JSON.stringify({ t: 'end', id: id }));
            setProgress(1, 1, '已发送：' + meta.name, t0, true);
            res();
            return;
          }
          drain(function () {
            var end = Math.min(off + CHUNK, buf.byteLength);
            try { dc.send(buf.slice(off, end)); } catch (e) { rej(e); return; }
            off = end;
            progress(off, buf.byteLength, '发送：' + meta.name, t0);
            pump();
          });
        })();
      });
    });
  }

  /* 背压：缓冲超过 1MB 时排队等待，避免撑爆内存导致崩溃 */
  function drain(cb) {
    if (!dc || dc.bufferedAmount < HIGH) { cb(); return; }
    var done = false;
    function go() { if (!done) { done = true; cb(); } }
    try { dc.addEventListener('bufferedamountlow', go, { once: true }); } catch (e) {}
    (function poll() {
      if (done) return;
      if (!dc || dc.readyState !== 'open') { go(); return; }
      if (dc.bufferedAmount < HIGH) { go(); return; }
      setTimeout(poll, 30);
    })();
  }

  /* ============================ 进度与列表 ============================ */
  var lastPaint = 0;
  function progress(done, total, name, t0) {
    var now = Date.now();
    if (now - lastPaint < 120 && done < total) return;     // 节流，减少重排
    lastPaint = now;
    setProgress(done, total, name, t0, done >= total);
  }
  function setProgress(done, total, name, t0, full) {
    var p = total ? Math.min(100, done / total * 100) : 0;
    E.bar.style.width = (full ? 100 : p) + '%';
    E.pct.textContent = (full ? 100 : Math.floor(p)) + '%';
    E.pname.textContent = name || '—';
    var sec = t0 ? (Date.now() - t0) / 1000 : 0;
    if (sec > 0.4 && done > 0) {
      var sp = done / sec;
      E.speed.textContent = fmt(sp) + '/s';
      E.eta.textContent = full ? '完成' : '剩余约 ' + Math.max(1, Math.ceil((total - done) / sp)) + ' 秒';
    } else { E.speed.textContent = '—'; E.eta.textContent = full ? '完成' : '—'; }
  }

  function updateSendBtn() {
    E.send.disabled = !(dc && dc.readyState === 'open') || !queue.length || sending;
  }

  function addToQueue(files) {
    var added = 0;
    Array.prototype.forEach.call(files, function (f) {
      if (!/^image\//.test(f.type) && !/\.(heic|heif|dng|tif|tiff|jpg|jpeg|png|webp|bmp)$/i.test(f.name)) return;
      var item = { file: f, url: '' };
      var row = document.createElement('div');
      row.className = 'item';
      row.innerHTML =
        '<div class="thumb">🖼</div>' +
        '<div class="meta"><div class="name">' + esc(f.name) + '</div>' +
        '<div class="sub"><span>' + fmt(f.size) + '</span><span class="tag">原图队列</span></div></div>' +
        '<button class="x" type="button" aria-label="移除">×</button>';
      var img = null;
      if (/^image\/(jpeg|png|webp|gif|bmp)$/i.test(f.type)) {
        try { item.url = URL.createObjectURL(f); img = new Image(); img.className = 'thumb'; img.src = item.url; row.replaceChild(img, row.firstChild); } catch (e) {}
      }
      row.querySelector('.x').addEventListener('click', function () {
        queue.splice(queue.indexOf(item), 1);
        if (item.url) URL.revokeObjectURL(item.url);
        E.queue.removeChild(row); updateSendBtn();
      });
      queue.push(item); E.queue.appendChild(row); added++;
    });
    if (added) { updateSendBtn(); toast('已加入 ' + added + ' 张原图', 'ok'); }
    else toast('未识别到图片文件', 'warn');
  }

  function addRecv(meta, blob) {
    var url = URL.createObjectURL(blob);
    var row = document.createElement('div');
    row.className = 'item';
    row.innerHTML =
      '<div class="thumb">🖼</div>' +
      '<div class="meta"><div class="name">' + esc(meta.name) + '</div>' +
      '<div class="sub"><span>' + fmt(meta.size) + '</span>' +
      '<span class="tag ' + (meta.mime === 'image/jpeg' ? 'exif' : '') + '">' + esc(meta.mime || '二进制') + '</span>' +
      '<span class="tag">已完整接收</span></div></div>' +
      '<button class="btn sm dl" type="button">下载</button>';
    if (/^image\//.test(meta.mime || '')) {
      var img = new Image(); img.className = 'thumb'; img.src = url;
      img.onerror = function () { var d = document.createElement('div'); d.className = 'thumb'; d.textContent = '🖼'; row.replaceChild(d, img); };
      row.replaceChild(img, row.firstChild);
    }
    row.querySelector('.dl').addEventListener('click', function () { save(url, meta.name); });
    var hint = E.recv.querySelector('.hint'); if (hint) hint.remove();
    E.recv.appendChild(row);
    jellyify(row.querySelector('.dl'));            // 动态按钮同样挂上玻璃面与光效层
    E.recvbar.classList.remove('hide');
  }

  function save(url, name) {
    var a = document.createElement('a');
    a.href = url; a.download = name || ('IMG_' + Date.now() + '.jpg');
    a.rel = 'noopener';
    document.body.appendChild(a); a.click();
    setTimeout(function () { document.body.removeChild(a); }, 1200);   // 不 revoke：供再次下载 / 预览
  }

  /* ============================ 重置 ============================ */
  function resetPeer() {
    if (retryTimer) clearTimeout(retryTimer), retryTimer = null;
    retries = 0; pendingCand = []; rx = null; acks = {};
    if (dc) { try { dc.close(); } catch (e) {} dc = null; }
    if (pc) { try { pc.close(); } catch (e) {} pc = null; }
  }

  /* ============================ 事件绑定 ============================ */
  E.gen.addEventListener('click', function () {
    var rm = (E.room.value || '').trim().toUpperCase();
    if (!/^[A-Z0-9_-]{3,12}$/.test(rm)) rm = randRoom();
    resetPeer(); startHost(rm);
    toast('已生成二维码，另一台设备扫码即可', 'ok');
  });

  E.join.addEventListener('click', function () {
    var rm = (E.room.value || '').trim().toUpperCase();
    if (!/^[A-Z0-9_-]{3,12}$/.test(rm)) { toast('请输入 3–12 位房间号', 'warn'); return; }
    resetPeer(); startGuest(rm);
  });

  E.copy.addEventListener('click', function () {
    var v = E.room.value || room;
    if (!v) { toast('还没有房间号', 'warn'); return; }
    var ok = function () { toast('房间号已复制', 'ok'); };
    if (navigator.clipboard && navigator.clipboard.writeText) navigator.clipboard.writeText(v).then(ok, fallback);
    else fallback();
    function fallback() {
      E.room.select();
      try { document.execCommand('copy'); ok(); } catch (e) { toast('请手动复制：' + v, 'warn'); }
    }
  });

  E.scan.addEventListener('click', openScan);
  E.scanclose.addEventListener('click', closeScan);

  E.file.addEventListener('change', function () { addToQueue(E.file.files); E.file.value = ''; });
  E.drop.addEventListener('dragover', function (e) { e.preventDefault(); E.drop.classList.add('over'); });
  E.drop.addEventListener('dragleave', function () { E.drop.classList.remove('over'); });
  E.drop.addEventListener('drop', function (e) {
    e.preventDefault(); E.drop.classList.remove('over');
    if (e.dataTransfer && e.dataTransfer.files) addToQueue(e.dataTransfer.files);
  });

  E.send.addEventListener('click', sendAll);
  E.clear.addEventListener('click', function () {
    queue.forEach(function (it) { if (it.url) URL.revokeObjectURL(it.url); });
    queue = []; E.queue.innerHTML = ''; updateSendBtn();
    E.bar.style.width = '0%'; E.pct.textContent = '0%'; E.pname.textContent = '等待开始';
    E.speed.textContent = '—'; E.eta.textContent = '—';
  });

  E.retry.addEventListener('click', function () {
    if (!role || !room) { toast('请先配对（生成二维码或加入房间）', 'warn'); return; }
    retries = 0;
    if (!pc) { role === 'host' ? startHost(room) : startGuest(room); return; }
    if (dc && dc.readyState === 'open') { toast('当前连接正常', 'ok'); return; }
    status('手动重连中…', 'warn');
    iceRestart();
    setTimeout(function () { if (role === 'guest') sig.send({ t: 'hello' }); }, 800);
  });

  E.saveall.addEventListener('click', function () {
    var btns = E.recv.querySelectorAll('.dl');
    Array.prototype.forEach.call(btns, function (b, i) { setTimeout(function () { b.click(); }, i * 550); });
  });

  /* 页面异常统一提示，避免静默失败 */
  window.addEventListener('error', function (e) {
    if (e && e.message) toast('出错：' + e.message, 'bad', 3600);
  });
  window.addEventListener('unhandledrejection', function (e) {
    var r = e && e.reason; if (r && /User denied|NotAllowed/i.test(String(r))) toast('摄像头权限被拒绝', 'warn');
  });
  window.addEventListener('pagehide', function () { resetPeer(); });

  /* 由链接参数自动入房：?r=XXXXXX */
  (function boot() {
    var r = '';
    try { r = new URLSearchParams(location.search).get('r') || ''; } catch (e) {}
    if (r && /^[A-Za-z0-9_-]{3,12}$/.test(r)) {
      room = r.toUpperCase(); E.room.value = room;
      setTimeout(function () { startGuest(room); }, 300);
    }
    updateSendBtn();
  })();
})();
