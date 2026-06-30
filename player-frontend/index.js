// ===== js/00-core-state.js =====
'use strict';

// 文件总览：
// 这是嵌入 iframe 内运行的播放器主前端，负责 Three.js 可视化、歌词舞台、3D 歌单架、控制面板和 EchoMusic 宿主桥接。
// 宿主只通过 postMessage 推送播放状态、歌词、队列和频谱；本文件不直接解码音频，也不直接持有真实播放源。
// 维护时优先确认数据来源：宿主快照负责业务状态，主循环负责视觉状态，控制命令最终都回传宿主执行。

// ============================================================
//  Global State
// ============================================================
// 真实音频元素在桥接模式下会被伪 audio 替换；旧播放器逻辑通过这个变量读取播放时间和状态。
var audio = null;
// UI 音效的 AudioContext 和上一次歌单架选择音效时间，用于限制交互音效触发频率。
var uiSfxCtx = null, lastShelfSelectSfxAt = 0;
// 普通频谱缓存长度，保留旧可视化代码需要的 FFT 尺寸。
var FFT_SIZE = 2048;
// 主频谱数据缓存，主循环会把宿主推送的 bins 映射到这个数组。
var frequencyData = new Uint8Array(FFT_SIZE / 2);
// 主波形数据缓存，主循环会把宿主推送的 waveform 映射到这个数组。
var timeDomainData = new Uint8Array(FFT_SIZE);
// 节拍检测专用 FFT 尺寸，保留给实时节拍引擎读取。
var BEAT_FFT_SIZE = 2048;
// 节拍检测频谱缓存，和普通频谱分开便于后续算法独立调参。
var beatFrequencyData = new Uint8Array(BEAT_FFT_SIZE / 2);
// 节拍检测波形缓存，用于 RMS、瞬态和实时节拍判断。
var beatTimeDomainData = new Uint8Array(BEAT_FFT_SIZE);
// 宿主频谱按 44.1kHz 采样率理解，保证频段划分和历史可视化逻辑一致。
var HOST_SPECTRUM_SAMPLE_RATE = 44100;
// 宿主频谱超过这个时间未更新就视为失效，避免暂停或失焦后沿用旧能量。
var HOST_SPECTRUM_TTL_MS = 650;
// 宿主频谱的最新一帧缓存；主循环每帧读取它来驱动低频、中频、高频和节拍效果。
var hostSpectrumFrame = { bins: [], waveform: [], rms: 0, peak: 0, updatedAt: 0 };
// 当前帧的低频、中频、高频、总能量和节拍脉冲，主循环每帧更新并同步给 shader。
var bass = 0, mid = 0, treble = 0, audioEnergy = 0, beatPulse = 0, prevEnergy = 0;
// 歌词“阳光溢光”效果的门限和包络状态，用于判断副歌或高能段落的持续提亮。
var lyricSunEnergy = 0, lyricSunTarget = 0, lyricSunHold = 0, lyricSunAvg = 0, lyricSunPeak = 0.55;
// 频段平滑后的能量，避免原始频谱跳变直接驱动视觉造成闪烁。
var smoothBass = 0, smoothMid = 0, smoothTreb = 0, smoothEnergy = 0;
// 动态峰值基线，用于把不同歌曲的能量归一化到相近视觉强度。
var bassPeak = 0.12, midPeak = 0.10, treblePeak = 0.08, energyPeak = 0.10;
var beatOnsetFlag = false;        // beat 上升沿瞬时标志,每帧消费一次
var lastStrongDrop = 0;           // 用于 burst 预设的强 drop 时刻

// 歌词行、歌词显示状态、是否有原生逐字歌词，以及当前歌词时间来源。
var lyricsLines = [], lyricsVisible = false, lyricsHasNativeKaraoke = false, lyricsTimingSource = 'none';
// 播放列表、当前播放队列、当前索引、播放状态和播放按钮忙碌锁。
var playlist = [], playQueue = [], currentIdx = -1, playing = false, playToggleBusy = false;
// 音量动画句柄和切歌 token；切歌 token 用于丢弃旧歌曲的异步 UI/封面回调。
var volumeTween = null, trackSwitchToken = 0;
// 歌单封面加载缓存，避免 3D 歌单架重复请求同一封面。
var playlistCoverCache = {};
// 本地视觉布局和歌词设置的 localStorage 键名。
var LYRIC_LAYOUT_STORE_KEY = 'mineradio-lyric-layout-v1';
// 视觉预设存档结构版本，用于兼容旧存档迁移。
var VISUAL_PRESET_SCHEMA = 'skull-preset-v2';
// 默认播放视觉预设索引。
var DEFAULT_PLAYBACK_VISUAL_PRESET = 0;
// 最大可用视觉预设索引，所有外部输入都会被限制到这个范围。
var MAX_VISUAL_PRESET_INDEX = 6;
// 播放队列面板固定状态的 localStorage 键名。
var PLAYLIST_PANEL_PIN_STORE_KEY = 'mineradio-playlist-panel-pinned-v1';
// 底部控制条自动隐藏偏好的 localStorage 键名。
var CONTROLS_AUTO_HIDE_STORE_KEY = 'mineradio-controls-auto-hide-v1';
// 自由相机配置的 localStorage 键名。
var FREE_CAMERA_STORE_KEY = 'mineradio-free-camera-v1';
// 把任意输入规整为合法视觉预设索引，异常值回退到 fallback 或默认预设。
function normalizeVisualPresetIndex(value, fallback) {
  // 先尝试转数值，外部存档可能是字符串、null 或损坏数据。
  var n = Number(value);
  // 第一次回退使用调用方传入的 fallback，fallback 也非法时再落到内置默认。
  if (!isFinite(n)) n = fallback == null ? DEFAULT_PLAYBACK_VISUAL_PRESET : Number(fallback);
  if (!isFinite(n)) n = DEFAULT_PLAYBACK_VISUAL_PRESET;
  // 最终四舍五入并钳制到可用预设范围，避免小数索引进入数组访问。
  return Math.round(clampRange(n, 0, MAX_VISUAL_PRESET_INDEX));
}
// 系统级“减少动态效果”偏好，后续动画逻辑可以据此降低运动强度。
var prefersReducedMotion = !!(window.matchMedia && window.matchMedia('(prefers-reduced-motion: reduce)').matches);
// 启动阶段性能打点列表，保留最近若干关键时间点供调试。
var appPerfMarks = [];
// 记录启动或关键流程的性能时间点，同时写入 Performance Timeline。
function markAppPerf(name) {
  try {
    // 使用 performance.now 获取相对页面启动的高精度时间。
    var value = performance.now();
    // 内存里保留简化后的整数时间，便于控制台查看。
    appPerfMarks.push({ name: name, value: Math.round(value) });
    // 浏览器支持时同步写 performance.mark，方便用 Performance 面板分析。
    if (performance && performance.mark) performance.mark('mineradio:' + name);
    // 只打印前 16 条，防止调试日志过多影响启动阶段。
    if (appPerfMarks.length <= 16) console.debug('[MineradioPerf]', name, Math.round(value) + 'ms');
  } catch (e) {}
}
// 脚本开始执行的首个性能标记。
markAppPerf('script-start');
// 安装启动阶段长任务观察器，用于定位首屏前 15 秒内的卡顿来源。
function installStartupLongTaskObserver() {
  try {
    // 不支持 PerformanceObserver 的环境直接跳过，保持兼容。
    if (!('PerformanceObserver' in window)) return;
    // 观察 longtask 条目并把启动早期的长任务打印到控制台。
    var observer = new PerformanceObserver(function(list){
      list.getEntries().forEach(function(entry){
        // 只关心启动早期，长期运行阶段由主循环性能统计负责。
        if (entry.startTime > 15000) return;
        console.debug('[MineradioPerf] longtask', Math.round(entry.startTime) + 'ms', Math.round(entry.duration) + 'ms');
      });
    });
    // longtask 只作为诊断工具，不参与业务逻辑。
    observer.observe({ entryTypes: ['longtask'] });
    // 16 秒后断开观察器，避免长期持有额外性能监听。
    setTimeout(function(){ try { observer.disconnect(); } catch (e) {} }, 16000);
  } catch (e) {}
}
// 启动时立即启用长任务观察，失败会被函数内部吞掉。
installStartupLongTaskObserver();
// 队列面板当前标签、播放模式和迷你队列面板开关。
var queueViewTab = 'queue', playMode = 'loop', miniQueueOpen = false;
// 多个列表渲染序号，用于丢弃异步批量渲染中的旧任务。
var miniQueueRenderSeq = 0, queueRenderSeq = 0, playlistRenderSeq = 0;
// 队列面板脏标记，表示数据变化后需要重绘。
var queuePanelDirty = false;
// 播放队列面板每批渲染数量，控制一次 DOM 更新规模。
var PLAYLIST_PANEL_BATCH_SIZE = 28;
// 当前队列面板允许渲染的上限，会随着懒加载逐步增加。
var playlistPanelRenderLimit = PLAYLIST_PANEL_BATCH_SIZE;
// 队列面板滚动懒加载监听是否已绑定。
var playlistPanelLazyBound = false;
// 歌单详情首屏渲染条数，避免一次性渲染超长歌单。
var PLAYLIST_DETAIL_INITIAL_RENDER = 64;
// 歌单详情后续每批追加渲染条数。
var PLAYLIST_DETAIL_BATCH_SIZE = 48;
// 平滑滚轮处理器是否已经绑定，防止重复监听。
var smoothWheelScrollBound = false;
// 封面处理和 AI 深度估计都是异步的，coverProcessToken 用来丢弃已经过期的图片加载或模型结果。
var coverProcessToken = 0, aiDepthPipeline = null, aiDepthReady = false, aiDepthBusy = false, aiDepthFailUntil = 0;
// AI 深度最近运行时间和最小间隔，防止频繁切歌时连续触发模型推理。
var aiDepthLastRunAt = 0, aiDepthMinGapMs = 18000;
// 从本地存储读取音量，读取失败或值非法时使用最大音量。
function readSavedVolume() {
  try {
    // 历史播放器使用 apex-player-volume 作为音量键，桥接模式继续兼容这个键。
    var v = parseFloat(localStorage.getItem('apex-player-volume'));
    // 音量必须位于 0..1，非法值回退到 1.0。
    return isFinite(v) ? Math.max(0, Math.min(1, v)) : 1.0;
  } catch (e) {
    return 1.0;
  }
}
// 读取布尔偏好，localStorage 中 '1' 表示 true，其余非空值表示 false。
function readBooleanPreference(key, fallback) {
  try {
    // 未保存时返回调用方传入的默认值。
    var raw = localStorage.getItem(key);
    if (raw == null) return !!fallback;
    return raw === '1';
  } catch (e) {
    return !!fallback;
  }
}
// 保存布尔偏好，使用 '1'/'0' 便于旧代码和手工调试识别。
function saveBooleanPreference(key, on) {
  try { localStorage.setItem(key, on ? '1' : '0'); } catch (e) {}
}
// 当前目标音量，启动时从本地存储恢复。
var targetVolume = readSavedVolume();
// 最近一次非静音音量，用于静音按钮恢复原音量。
var lastNonZeroVolume = targetVolume > 0.01 ? targetVolume : 0.8;
// 音量浮层自动关闭计时器。
var volumeCloseTimer = null;

// 宿主频谱模式: 插件端不再生成、解码或缓存节奏分析结果。
// 普通 beatMap 缓存，保留结构是为了兼容后续 tickBeatMap 和旧接口。
var beatMapCache = {};       // { songId: { kicks: [t1, t2, ...], duration: ... } }
var currentBeatMap = null;   // 当前播放的歌的 beatMap
var beatMapNextIdx = 0;      // 下一个待触发的 kick index
var beatMapToken = 0;        // 取消旧分析
// 普通 beatMap 分析定时器，切歌或进入 DJ 模式时会取消。
var beatAnalysisTimer = null;
// DJ 模式下的 beatMap 缓存，和普通模式隔离，避免不同分析策略互相污染。
var djBeatMapCache = {};
// 当前 DJ beatMap 和下一个要消费的节拍索引。
var currentDjBeatMap = null;
var djBeatMapNextIdx = 0;
// DJ 模式下用于视觉脉冲的独立节拍索引。
var djBeatPulseNextIdx = 0;
// DJ beatMap 异步分析 token，切歌或退出 DJ 时递增以取消旧结果。
var djBeatMapToken = 0;
// DJ beatMap 分析定时器句柄。
var djBeatAnalysisTimer = null;
// 节拍镜头状态：保存预解析节拍、实时节拍、镜头冲击包络和统计信息。
var beatCam = {
  nextIdx: 0,
  events: [],
  punch: 0,
  lookahead: 0.075,
  lastTriggerAt: -10,
  lastRealtimeAt: -10,
  minInterval: 0.500,
  fallbackMinInterval: 0.320,
  realtimeMinInterval: 0.460,
  realtimeMergeWindow: 0.135,
  attack: 0.028,
  hold: 0.030,
  release: 0.185,
  thetaKick: 0,
  phiKick: 0,
  radiusKick: 0,
  rollKick: 0,
  prevAudioTime: -1,
  stats: { map: 0, live: 0, merged: 0, liveBlocked: 0 }
};
// 实时镜头强度的均值、峰值和上一帧原始值，用于稳定镜头触发。
var liveCamAvg = 0, liveCamPeak = 0.28, liveCamLastRaw = 0;
// 电影镜头动态缩放统计，综合持续能量和低频能量决定镜头幅度。
var cinemaDynamics = { avg: 0, lowAvg: 0, peak: 0.30, scale: 0.82 };
// 当前歌曲的电影镜头画像，用较慢的包络描述能量、低频、人声、旋律和密度。
var cinemaTrackProfile = {
  scale: 1.0,
  target: 1.0,
  nameHint: 1.0,
  frames: 0,
  energyAvg: 0,
  lowAvg: 0,
  vocalAvg: 0,
  melodyAvg: 0,
  punchPeak: 0.10,
  density: 0
};
// 实时节拍检测器的多频段包络和统计状态。
var rtBeat = {
  subFast: 0, subSlow: 0, lowFast: 0, lowSlow: 0,
  bodyFast: 0, bodySlow: 0, vocalFast: 0, vocalSlow: 0, snapFast: 0, snapSlow: 0,
  prevSub: 0, prevLow: 0, prevBody: 0, prevVocal: 0, prevSnap: 0, prevRms: 0,
  onsetAvg: 0.012, onsetPeak: 0.060,
  subPeak: 0.14, lowPeak: 0.18, bodyPeak: 0.16, vocalPeak: 0.16, snapPeak: 0.14,
  lastHitAt: -10,
  tempoGap: 0,
  tempoConfidence: 0,
  beatCount: 0,
  primedFrames: 0,
  warmupUntil: 0,
  pulse: 0,
  score: 0,
  stats: { hits: 0, blocked: 0, assisted: 0, strong: 0, rejected: 0 }
};
// DJ 模式状态，记录当前歌曲键、节拍稳定度、段落能量和视觉脉冲。
var djMode = {
  active: false,
  songKey: '',
  startedAt: 0,
  lastNoticeAt: -100000,
  tempoGap: 0,
  tempoConfidence: 0,
  sectionEnergy: 0,
  sectionLow: 0,
  sectionChange: 0,
  visualPulse: 0,
  lastBeatAt: -10
};

// 为 DJ 模式生成稳定歌曲键，优先使用本地键，其次按来源和歌曲标识组合。
function djSongKey(song) {
  if (!song) return '';
  // 本地歌曲用 localKey，避免不同本地文件只靠歌名冲突。
  if (song.localKey) return 'local:' + song.localKey;
  // QQ 音乐优先使用 mid/songmid，缺失时降级到 id 或标题歌手组合。
  if (songProviderKey(song) === 'qq') return 'qq:' + (song.mid || song.songmid || song.id || (song.name + '|' + song.artist));
  // 其他来源至少使用 id 或歌曲名作为缓存键。
  return 'song:' + (song.id || song.name || '');
}

// 重置 DJ 模式下的实时量表和视觉脉冲状态。
function resetDjModeMeter() {
  djMode.tempoGap = 0;
  djMode.tempoConfidence = 0;
  djMode.sectionEnergy = 0;
  djMode.sectionLow = 0;
  djMode.sectionChange = 0;
  djMode.visualPulse = 0;
  djMode.lastBeatAt = -10;
}

// 清空当前 DJ beatMap 指针，通常在退出 DJ、切歌或取消分析时调用。
function resetDjBeatMapState() {
  currentDjBeatMap = null;
  djBeatMapNextIdx = 0;
  djBeatPulseNextIdx = 0;
}

// 取消正在等待的 DJ beatMap 分析任务，避免旧歌曲的延迟任务继续运行。
function cancelDjBeatAnalysisTimer() {
  if (djBeatAnalysisTimer) {
    clearTimeout(djBeatAnalysisTimer);
    djBeatAnalysisTimer = null;
  }
}

// 切换 DJ 模式，并按模式切换清理普通 beatMap 或 DJ beatMap 的状态。
function setDjModeActive(active, song) {
  // active 统一转布尔，song 只在开启 DJ 模式时用于生成 songKey。
  active = !!active;
  var key = active ? djSongKey(song) : '';
  // 模式开关或歌曲变化都视为状态变化，需要重置 DJ 量表。
  var changed = djMode.active !== active || djMode.songKey !== key;
  djMode.active = active;
  djMode.songKey = key;
  if (changed) {
    djMode.startedAt = performance.now();
    resetDjModeMeter();
  }
  if (active) {
    // DJ 模式接管节拍逻辑，普通 beatMap 要停掉，避免双重触发镜头。
    currentBeatMap = null;
    beatMapNextIdx = 0;
    cancelBeatAnalysisTimer();
    hideBeatChip();
  } else {
    // 退出 DJ 时递增 token 并清理 DJ 专用分析状态。
    djBeatMapToken++;
    cancelDjBeatAnalysisTimer();
    resetDjBeatMapState();
  }
}

// DJ 模式开启时低频提示用户当前处于离线锁拍模式。
function maybeAnnounceDjMode() {
  if (!djMode.active) return;
  // 提示至少间隔 8 秒，避免频繁刷新或切换时刷屏。
  var now = performance.now();
  if (now - djMode.lastNoticeAt > 8000) {
    djMode.lastNoticeAt = now;
    showToast('DJ Mode · 离线锁拍');
  }
}

// fx 状态: 预设 + 主滑块 + 开关 + 三态
// 用户可调视觉参数的默认值。fx 会在此基础上叠加本地存档，并在控制台、shader 和布局逻辑之间共享。
var fxDefaults = {
  // 默认视觉预设索引，启动时会根据存档覆盖。
  preset: DEFAULT_PLAYBACK_VISUAL_PRESET,            // 0=专辑封面，1=滚筒，2=星球，3=虚空，4=唱片，5=星河，6=安魂
  // 主视觉强度，作为低频、中频、高频映射到 shader 时的总倍率。
  intensity: 0.85,
  // 电影镜头震动幅度，影响节拍镜头和相机动态。
  cinemaShake: 0.5,
  // 粒子景深位移倍率，主要影响封面深度纹理带来的 Z 轴层次。
  depth: 1.0,
  // 封面纹理处理分辨率倍率，越高越清晰但 CPU/canvas 成本更高。
  coverResolution: 1.55,
  // 粒子点大小、运动速度、扭曲、颜色增益、散射和背景淡化的基础滑条值。
  point: 1.0, speed: 1.0, twist: 0.0, color: 1.10, scatter: 0.0, bgFade: 0.20,
  // 泛光强度，后续会同步给粒子材质和辉光层。
  bloomStrength: 0.62,
  // 歌词辉光基础强度。
  lyricGlowStrength: 0.28,
  // 3D 歌词整体缩放。
  lyricScale: 1.0,
  // 3D 歌词 X 轴偏移。
  lyricOffsetX: 0,
  // 3D 歌词 Y 轴偏移。
  lyricOffsetY: 0,
  // 3D 歌词 Z 轴偏移，用于控制歌词离相机远近。
  lyricOffsetZ: 0,
  // 3D 歌词绕 X 轴倾斜角。
  lyricTiltX: 0,
  // 3D 歌词绕 Y 轴倾斜角。
  lyricTiltY: 0,
  // 歌词主色模式，auto 表示从封面或主题自动取色。
  lyricColorMode: 'auto',
  // 手动歌词主色。
  lyricColor: '#a9b8c8',
  // 当前歌词高亮色模式，auto 表示自动取色。
  lyricHighlightMode: 'auto',
  // 手动歌词高亮色。
  lyricHighlightColor: '#fac900',
  // 歌词辉光颜色是否跟随歌词高亮色。
  lyricGlowLinked: true,
  // 手动歌词辉光颜色。
  lyricGlowColor: '#008aff',
  // 歌词字体族预设标识。
  lyricFont: 'hei',
  // 歌词字间距倍率。
  lyricLetterSpacing: 0,
  // 歌词行高倍率。
  lyricLineHeight: 1.0,
  // 歌词字重。
  lyricWeight: 900,
  // 主视觉染色模式，auto 表示跟随封面色。
  visualTintMode: 'auto',
  // 手动主视觉染色。
  visualTintColor: '#9db8cf',
  // UI 强调色，影响按钮、滑条和歌单架点缀。
  uiAccentColor: '#ffffff',
  // 视觉控制台图标颜色。
  visualIconColor: '#ffffff',
  // 背景颜色模式，cover 表示从封面取色，custom 表示使用用户颜色。
  backgroundColorMode: 'cover',
  // 自定义背景底色。
  backgroundColor: '#000000',
  // 自定义背景透明度。
  backgroundOpacity: 1,
  // 底部玻璃控制条色差位移强度。
  controlGlassChromaticOffset: 90,
  // 是否明确启用自定义背景颜色。
  backgroundColorCustom: false,
  // 旧版自定义背景图片字段，仍用于兼容存档。
  backgroundImage: '',
  // 新版自定义背景媒体对象，可表示图片或视频。
  backgroundMedia: null,
  // 壁纸模式开关，当前开发锁会强制关闭。
  wallpaperMode: false,
  // 壁纸模式透明度，保留给旧配置兼容。
  wallpaperOpacity: 1,
  // 各类视觉特效开关：浮空粒子、电影镜头、边缘、AI 深度、泛光和歌词辉光。
  floatLayer: false, cinema: true, edge: false, aiDepth: false, bloom: false, lyricGlow: true,
  // 歌词辉光是否随节拍增强。
  lyricGlowBeat: true,
  // 是否启用歌词周围的辉光粒子。
  lyricGlowParticles: false,
  // 歌词相机锁定开关，开启后歌词相机不会随部分镜头效果移动。
  lyricCameraLock: false,
  // 是否显示 3D 粒子歌词。
  particleLyrics: true,    // v7.2: 粒子歌词
  // 是否启用背面封面粒子层。
  backCover: false,        // 旧的封面背面粒子层关闭；浮空粒子层会跟随封面翻转
  // 3D 歌单架模式，side 表示右侧侧栏。
  shelf: 'side',
  // 歌单架相机跟随模式。
  shelfCameraMode: 'static',
  // 歌单架出现策略，always 表示始终可见或可触发。
  shelfPresence: 'always',
  // 歌单架整体缩放。
  shelfSize: 1,
  // 歌单架 X 轴用户偏移。
  shelfOffsetX: 0,
  // 歌单架 Y 轴用户偏移。
  shelfOffsetY: 0,
  // 歌单架 Z 轴用户偏移。
  shelfOffsetZ: 0,
  // 歌单架绕 Y 轴角度，单位在后续同步时转换。
  shelfAngleY: -15,
  // 用户是否手动改过歌单架角度，用于区分自动布局和用户设置。
  shelfAngleYManual: false,
  // 歌单架整体不透明度。
  shelfOpacity: 1,
  // 歌单架卡片背景不透明度。
  shelfBgOpacity: 0.90,
  // 歌单架强调色。
  shelfAccentColor: '#ffffff',
  // 后台渲染策略，auto/keep/release 等模式会影响主循环和缓存回收。
  performanceBackground: 'auto',
  // 渲染质量档位。
  performanceQuality: 'high',
  // 后台是否保持动态背景，不保持时会进入深度省电模式。
  liveBackgroundKeep: false,
};
// 内置用户视觉存档的显示名称。
var PACKAGED_DEFAULT_USER_FX_ARCHIVE_NAME = '默认测试';
// 内置用户视觉存档的导出时间戳，用于展示和排序。
var PACKAGED_DEFAULT_USER_FX_ARCHIVE_EXPORTED_AT = 1782276031784;
// 内置用户视觉存档的保存时间戳。
var PACKAGED_DEFAULT_USER_FX_ARCHIVE_SAVED_AT = 1782273019045;
// 打包内置的默认视觉快照，Object.freeze 防止运行期误改模板对象。
var PACKAGED_DEFAULT_FX_SNAPSHOT = Object.freeze({
  // 快照版本字段，用于导入或恢复默认时判断是否需要迁移。
  visualPresetSchema: VISUAL_PRESET_SCHEMA,
  // 以下字段对应 fxDefaults 的一份稳定副本，作为“恢复默认”和内置存档的源数据。
  preset: DEFAULT_PLAYBACK_VISUAL_PRESET,
  intensity: 0.85,
  cinemaShake: 0.5,
  depth: 1,
  coverResolution: 1.55,
  point: 1,
  speed: 1,
  twist: 0,
  color: 1.1,
  scatter: 0,
  bgFade: 0.2,
  bloomStrength: 0.62,
  lyricGlowStrength: 0.28,
  lyricScale: 1,
  lyricOffsetX: 0,
  lyricOffsetY: 0,
  lyricOffsetZ: 0,
  lyricTiltX: 0,
  lyricTiltY: 0,
  lyricCameraLock: false,
  lyricColorMode: 'auto',
  lyricColor: '#a9b8c8',
  lyricHighlightMode: 'auto',
  lyricHighlightColor: '#fac900',
  lyricGlowLinked: true,
  lyricGlowColor: '#008aff',
  lyricFont: 'hei',
  lyricLetterSpacing: 0,
  lyricLineHeight: 1,
  lyricWeight: 900,
  visualTintMode: 'auto',
  visualTintColor: '#9db8cf',
  uiAccentColor: '#ffffff',
  visualIconColor: '#ffffff',
  backgroundColorMode: 'cover',
  backgroundColor: '#000000',
  backgroundOpacity: 1,
  controlGlassChromaticOffset: 90,
  backgroundColorCustom: false,
  floatLayer: false,
  cinema: true,
  edge: false,
  aiDepth: false,
  bloom: false,
  lyricGlow: true,
  lyricGlowBeat: true,
  lyricGlowParticles: false,
  performanceBackground: 'auto',
  performanceQuality: 'high',
  liveBackgroundKeep: false,
  particleLyrics: true,
  backCover: false,
  shelf: 'side',
  shelfCameraMode: 'static',
  shelfPresence: 'always',
  shelfSize: 1,
  shelfOffsetX: 0,
  shelfOffsetY: 0,
  shelfOffsetZ: 0,
  shelfAngleY: -15,
  shelfAngleYManual: false,
  shelfOpacity: 1,
  shelfBgOpacity: 0.9,
  shelfAccentColor: '#ffffff'
});
// 返回打包默认快照的浅拷贝，避免调用方直接修改冻结模板。
function clonePackagedDefaultFxSnapshot() {
  return Object.assign({}, PACKAGED_DEFAULT_FX_SNAPSHOT);
}
// 读取打包默认歌词布局时复用视觉快照，保持恢复默认的入口一致。
function packagedDefaultLyricLayoutRaw() {
  return clonePackagedDefaultFxSnapshot();
}
// 开发期锁定的视觉字段；锁定字段会在读取存档后被强制归一化。
var DEVELOPMENT_LOCKED_FX = {
  // 壁纸模式当前不允许被存档重新开启。
  wallpaperMode: true
};
// 判断某个视觉字段是否被开发锁强制接管。
function isDevelopmentLockedFx(key) {
  return !!DEVELOPMENT_LOCKED_FX[key];
}
// 把开发锁字段恢复到允许的运行态。
function normalizeDevelopmentLockedFxState() {
  // fx 尚未初始化时直接跳过，避免启动顺序中的空引用。
  if (!fx) return;
  // 壁纸模式在当前桥接播放器中固定关闭。
  fx.wallpaperMode = false;
}
// 从本地布局存档里读取上次使用的视觉预设索引。
function readSavedPlaybackVisualPreset() {
  try {
    // 存档损坏时 JSON.parse 会抛错，catch 中回退默认预设。
    var raw = JSON.parse(localStorage.getItem(LYRIC_LAYOUT_STORE_KEY) || '{}') || {};
    // 旧用户没有保存 preset 时直接使用默认播放预设。
    if (!Object.prototype.hasOwnProperty.call(raw, 'preset')) return DEFAULT_PLAYBACK_VISUAL_PRESET;
    // 先做合法范围归一化，再处理历史版本迁移。
    var savedPreset = normalizeVisualPresetIndex(raw.preset, DEFAULT_PLAYBACK_VISUAL_PRESET);
    // 旧 schema 中的 3 号预设语义变化过，未带新版本号时迁移到 5 号。
    if (savedPreset === 3 && raw.visualPresetSchema !== VISUAL_PRESET_SCHEMA) savedPreset = 5;
    return savedPreset;
  } catch (e) {
    return DEFAULT_PLAYBACK_VISUAL_PRESET;
  }
}
// 启动时确定的播放视觉预设，后续用于首屏和存档同步。
var playbackVisualPreset = readSavedPlaybackVisualPreset();
// 运行期视觉状态：所有滑条、开关、预设和布局设置最终都会同步到这个对象。
var fx = Object.assign({}, fxDefaults, readSavedLyricLayout());
// 读取用户存档后立刻应用开发锁，保证后续模块看到的是可用状态。
normalizeDevelopmentLockedFxState();
// 预设切换动画状态，from/to 记录切换前后预设，duration 控制过渡时长。
var presetTransition = { active:false, start:-10, duration:0.92, from:0, to:0 };
// 底部控制条自动隐藏偏好。
var controlsAutoHide = readBooleanPreference(CONTROLS_AUTO_HIDE_STORE_KEY, false);
// 鼠标是否正悬停在控制条区域。
var controlsHovering = false;
// 控制条隐藏延迟计时器。
var controlsHideTimer = null;
// 最近一次控制区域指针移动时间。
var controlsLastMoveAt = 0;
// 歌单架交互期间临时抑制控制条自动隐藏的截止时间。
var controlsShelfSuppressUntil = 0;
// 鼠标指针自动隐藏计时器。
var cursorHideTimer = null;
// 鼠标静止多久后隐藏指针。
var CURSOR_HIDE_DELAY = 2500;
// 视觉控制台是否固定展开。
var fxPanelPinned = false;
// 播放队列面板是否固定展开，从本地偏好恢复。
var playlistPanelPinned = readBooleanPreference(PLAYLIST_PANEL_PIN_STORE_KEY, false);
// 沉浸模式开关。
var immersiveMode = false;
// 进入沉浸模式前需要暂存的界面状态，退出时按这里恢复。
var immersiveState = {
  shelfMode: null,
  shelfPinnedOpen: false,
  lyrics: true,
  controlsAutoHide: true,
  bottomVisible: false
};

// 鼠标 / 指针视差
// 当前已经平滑后的指针视差，用于镜头和歌单架轻微跟随。
var pointerParallax = { x:0, y:0 };
// 指针视差目标值，mousemove 只写目标，主循环负责缓动。
var pointerTarget = { x:0, y:0 };
// 头部/封面视差状态，active 表示当前是否启用头部追踪式视差。
var headParallax = { x:0, y:0, active:false };
// 头部视差的中性点，用于把输入坐标转成相对位移。
var headNeutral = null;

// 给对象上的某个数值字段打一段短脉冲，常用于按钮、镜头或视觉状态的瞬时反馈。
function pulseObjectValue(target, key, amount, duration) {
  // 目标对象不存在时直接跳过，便于在可选模块中安全调用。
  if (!target) return;
  // 脉冲先立刻抬到指定强度，再由动画归零。
  target[key] = Math.max(target[key] || 0, amount || 1);
  if (window.gsap) {
    // 有 GSAP 时使用补间，覆盖同字段旧动画。
    window.gsap.killTweensOf(target, key);
    var vars = { duration: duration || 0.42, ease: 'power3.out' };
    vars[key] = 0;
    window.gsap.to(target, vars);
  } else {
    // 没有 GSAP 时降级为延迟清零，不保证平滑但保持状态不会卡住。
    setTimeout(function(){ if (target) target[key] = 0; }, (duration || 0.42) * 1000);
  }
}

// 桌面宿主窗口状态，影响后台省电、全屏歌词相机校准和恢复策略。
var desktopRuntimeState = {
  desktop: false,
  minimized: false,
  visible: true,
  focused: true,
  fullscreen: false
};
// 渲染器当前功耗模式缓存，避免重复 setSize/setPixelRatio。
var renderPowerState = { mode: '', width: 0, height: 0, pixelRatio: 0 };
// 后台缓存裁剪的延迟计时器。
var backgroundCacheTrimTimer = 0;
// 后台省电和缓存裁剪的运行时统计。它既用于调试，也用于避免隐藏窗口继续保留过多纹理和缓存。
var runtimePerfState = {
  lastCacheTrimAt: 0,
  cacheTrimCount: 0,
  lastCacheTrimReason: '',
  lastHeapSampleAt: 0,
  heapMB: 0,
  cacheCounts: {}
};
function isDeepBackgroundMode() {
  // 深度后台模式会显著降低渲染频率并触发缓存裁剪；用户选择“后台保持”时跳过该策略。
  if (isLiveBackgroundKeepMode()) return false;
  return !!(document.hidden || desktopRuntimeState.minimized || desktopRuntimeState.visible === false);
}
function currentPerformanceBackgroundMode() {
  // 统一读取性能后台策略，兼容旧的 liveBackgroundKeep 开关。
  return normalizePerformanceBackgroundMode(fx && fx.performanceBackground, fx && fx.liveBackgroundKeep === true);
}
// 判断后台是否保持动态背景，保持时不进入深度睡眠。
function isLiveBackgroundKeepMode() {
  return currentPerformanceBackgroundMode() === 'keep';
}
// 判断后台是否尽快释放资源。
function isBackgroundReleaseMode() {
  return currentPerformanceBackgroundMode() === 'release';
}
// 当前是否因为 document.hidden 进入后台优化状态。
function isHiddenForBackgroundOptimization() {
  return !!(document.hidden && !isLiveBackgroundKeepMode());
}
// 预留的可见后台模式判断，当前固定关闭。
function isVisibleBackgroundMode() {
  return false;
}
function updateRenderPowerClasses() {
  // CSS 类和 renderer 电源模式分开维护：类负责界面表现，renderer 负责实际像素比与刷新策略。
  document.body.classList.toggle('render-deep-sleep', isDeepBackgroundMode());
  document.body.classList.toggle('render-background-eco', isVisibleBackgroundMode());
}
function safeObjectKeys(obj) {
  // 某些缓存对象可能被外部污染或置空，统一保护 Object.keys。
  try { return obj ? Object.keys(obj) : []; } catch (e) { return []; }
}
// 向保护表写入一个字符串 key，空 key 会被忽略。
function markProtectedKey(map, key) {
  if (key) map[String(key)] = true;
}
// 收集当前仍在使用的封面 URL，缓存裁剪时不能删除这些封面的加载记录。
function collectProtectedCoverUrls() {
  // 使用无原型对象作为集合，避免和内置属性名冲突。
  var keep = Object.create(null);
  // 本地 helper 统一做空值保护。
  function mark(url) { if (url) keep[String(url)] = true; }
  try {
    // 当前播放歌曲的多个尺寸封面都要保护，因为 UI 和 3D 卡片可能使用不同尺寸。
    var song = (typeof currentCoverSong === 'function') ? currentCoverSong() : (playQueue && currentIdx >= 0 ? playQueue[currentIdx] : null);
    if (song) {
      mark(song.cover);
      if (typeof songCoverSrc === 'function') {
        mark(songCoverSrc(song, 60));
        mark(songCoverSrc(song, 360));
        mark(songCoverSrc(song, 400));
      }
    }
    if (typeof currentCoverSource !== 'undefined' && currentCoverSource && currentCoverSource.src) mark(currentCoverSource.src);
    // 当前已渲染的 3D 歌单卡片封面也需要保护，避免卡片贴图突然丢失。
    if (shelfManager && shelfManager.getCards) {
      shelfManager.getCards().forEach(function(card){
        if (card && card.item) mark(card.item.cover);
      });
    }
  } catch (e) {}
  return keep;
}
// 收集当前播放附近和 DJ 模式使用中的 beatMap key，避免裁剪掉马上要消费的节拍数据。
function collectProtectedBeatMapKeys() {
  var keep = Object.create(null);
  try {
    // 当前歌曲前后 5 首都保留，兼顾上一首/下一首快速切换。
    if (typeof beatMapSongKey === 'function' && playQueue && playQueue.length) {
      var start = Math.max(0, currentIdx - 5);
      var end = Math.min(playQueue.length - 1, currentIdx + 5);
      for (var i = start; i <= end; i++) markProtectedKey(keep, beatMapSongKey(playQueue[i]));
    }
    if (typeof djMode !== 'undefined' && djMode && djMode.songKey) markProtectedKey(keep, djMode.songKey);
  } catch (e) {}
  return keep;
}
// 收藏封面深度已迁移到 IndexedDB，无需内存保护裁剪。
// 通用对象缓存裁剪：保留 keep 个未保护项，返回实际删除数量。
function trimObjectCache(cache, keep, protectedKeys, skipRecord) {
  // 空缓存或数量未超过上限时无需裁剪。
  var keys = safeObjectKeys(cache);
  if (!cache || keys.length <= keep) return 0;
  // drop 是需要删除的数量，按 keys 顺序从旧项开始尝试删除。
  var drop = keys.length - keep;
  var dropped = 0;
  for (var i = 0; i < keys.length && drop > 0; i++) {
    var key = keys[i];
    // 保护表命中的 key 不能删除。
    if (protectedKeys && protectedKeys[key]) continue;
    var rec = cache[key];
    // skipRecord 允许调用方保护正在 loading 的条目等特殊状态。
    if (skipRecord && skipRecord(rec, key)) continue;
    delete cache[key];
    drop--;
    dropped++;
  }
  return dropped;
}
// 收集当前运行时性能快照，供 window.__mineradioPerfSnapshot 调试调用。
function collectRuntimePerfSnapshot(now) {
  // now 可由调用方传入，避免同一帧内重复读取 performance.now。
  now = now || performance.now();
  // 统计各类缓存数量，便于观察裁剪是否生效。
  runtimePerfState.cacheCounts = {
    playlistCovers: safeObjectKeys(playlistCoverCache).length,
    beatMaps: safeObjectKeys(beatMapCache).length,
    djBeatMaps: safeObjectKeys(djBeatMapCache).length
  };
  if (performance && performance.memory && now - runtimePerfState.lastHeapSampleAt > 12000) {
    // Chrome/Electron 下可读取 JS 堆内存；采样间隔较长，避免频繁触碰性能接口。
    runtimePerfState.lastHeapSampleAt = now;
    runtimePerfState.heapMB = Math.round((performance.memory.usedJSHeapSize || 0) / 1048576);
  }
  return {
    // 主循环渲染状态由后面模块创建，启动早期不存在时返回 null。
    render: (typeof renderPerfState !== 'undefined') ? {
      mode: renderPerfState.mode,
      fps: renderPerfState.fps,
      skipped: renderPerfState.skipped,
      longFrames: renderPerfState.longFrames
    } : null,
    runtime: runtimePerfState,
    // renderer.info 提供 GPU 资源和 draw call 统计。
    renderer: (typeof renderer !== 'undefined' && renderer && renderer.info) ? {
      geometries: renderer.info.memory && renderer.info.memory.geometries,
      textures: renderer.info.memory && renderer.info.memory.textures,
      calls: renderer.info.render && renderer.info.render.calls,
      triangles: renderer.info.render && renderer.info.render.triangles
    } : null,
    // 当前视口和实际 canvas 像素信息，用于排查 DPR 和后台省电尺寸。
    viewport: (typeof renderer !== 'undefined' && renderer && renderer.domElement) ? {
      width: innerWidth,
      height: innerHeight,
      devicePixelRatio: window.devicePixelRatio || 1,
      renderPixelRatio: renderer.getPixelRatio ? Number(renderer.getPixelRatio().toFixed(3)) : 0,
      canvasWidth: renderer.domElement.width || 0,
      canvasHeight: renderer.domElement.height || 0,
      renderPixels: (renderer.domElement.width || 0) * (renderer.domElement.height || 0),
      targetFps: (typeof getAdaptiveRenderFps === 'function') ? getAdaptiveRenderFps() : 0,
      interactionBoost: (typeof isRenderInteractionActive === 'function') ? isRenderInteractionActive() : false,
      interactionReason: (typeof renderInteractionReason !== 'undefined') ? renderInteractionReason : ''
    } : null,
    deepSleep: isDeepBackgroundMode()
  };
}
// 暴露调试函数，控制台可直接调用查看当前性能和缓存状态。
window.__mineradioPerfSnapshot = collectRuntimePerfSnapshot;
// 执行一次运行时缓存裁剪，aggressive=true 时用于后台深度清理。
function trimRuntimeCaches(reason, aggressive) {
  // 先收集保护集合，确保当前播放和当前可见卡片使用的资源不被删除。
  var protectedCovers = collectProtectedCoverUrls();
  var protectedBeats = collectProtectedBeatMapKeys();
  var dropped = 0;
  // 播放列表封面缓存较大，后台时保留更少；正在加载的记录暂不删除。
  dropped += trimObjectCache(playlistCoverCache, aggressive ? 72 : 180, protectedCovers, function(rec){
    return rec && rec.loading;
  });
  // 普通 beatMap 和 DJ beatMap 分别裁剪，避免大量歌曲切换后积累。
  dropped += trimObjectCache(beatMapCache, aggressive ? 12 : 36, protectedBeats);
  dropped += trimObjectCache(djBeatMapCache, aggressive ? 4 : 12, protectedBeats);
  // 激进裁剪时释放 renderer 内部 renderLists，降低隐藏窗口的 GPU/CPU 占用。
  if (aggressive && typeof renderer !== 'undefined' && renderer && renderer.renderLists && renderer.renderLists.dispose) {
    try { renderer.renderLists.dispose(); } catch (e) {}
  }
  runtimePerfState.lastCacheTrimAt = performance.now();
  runtimePerfState.cacheTrimCount += 1;
  runtimePerfState.lastCacheTrimReason = reason || (aggressive ? 'deep' : 'active');
  // 裁剪后立即刷新一次快照，便于调试看到最新数量。
  collectRuntimePerfSnapshot(runtimePerfState.lastCacheTrimAt);
  return dropped;
}
// 只有处于深度后台模式时才执行后台视觉缓存裁剪。
function trimVisualCachesForBackground() {
  if (!isDeepBackgroundMode()) return;
  trimRuntimeCaches('deep-background', true);
}
// 延迟触发后台缓存裁剪，避免 visibility/blur 事件中同步做重活。
function scheduleBackgroundCacheTrim() {
  if (!isDeepBackgroundMode()) return;
  // 多次进入后台只保留最后一个计时器。
  if (backgroundCacheTrimTimer) clearTimeout(backgroundCacheTrimTimer);
  backgroundCacheTrimTimer = setTimeout(function(){
    backgroundCacheTrimTimer = 0;
    trimVisualCachesForBackground();
  }, 900);
}
function maybeTrimRuntimeCaches(now) {
  // 主循环定期调用这里；真正的裁剪会避开当前封面和当前 3D 歌单卡片仍在使用的资源。
  now = now || performance.now();
  var deep = isDeepBackgroundMode();
  // 后台裁剪间隔更短，release 模式最激进；前台只做低频维护性裁剪。
  var gap = deep ? (isBackgroundReleaseMode() ? 3600 : 7000) : 45000;
  // 启动前 30 秒不做前台裁剪，避免首屏阶段和资源加载竞争。
  if (!deep && now < 30000) return;
  if (now - runtimePerfState.lastCacheTrimAt < gap) return;
  trimRuntimeCaches(deep ? (isBackgroundReleaseMode() ? 'release-frame' : 'deep-frame') : 'active-frame', deep);
}
// 根据当前后台状态调整 renderer 尺寸和像素比。
function applyRendererPowerMode() {
  // renderer 在后面 Three.js 场景模块才创建，提前调用时安全跳过。
  if (typeof renderer === 'undefined' || !renderer) return;
  var deep = isDeepBackgroundMode();
  // 深度睡眠时把 canvas 缩到 4x4，保留渲染链路但大幅降低像素成本。
  var width = deep ? 4 : Math.max(1, innerWidth);
  var height = deep ? 4 : Math.max(1, innerHeight);
  var pixelRatio = getRenderPixelRatio();
  var mode = deep ? 'sleep' : 'active';
  // 状态未变化时避免重复 setSize，减少 layout 和 WebGL 状态切换。
  if (renderPowerState.mode === mode && renderPowerState.width === width && renderPowerState.height === height && Math.abs(renderPowerState.pixelRatio - pixelRatio) < 0.001) return;
  renderPowerState = { mode: mode, width: width, height: height, pixelRatio: pixelRatio };
  renderer.setPixelRatio(pixelRatio);
  renderer.setSize(width, height, false);
  // uPixel 影响 shader 点大小，需要和 renderer DPR 保持同步。
  if (typeof uniforms !== 'undefined' && uniforms && uniforms.uPixel) uniforms.uPixel.value = renderer.getPixelRatio();
  if (deep) {
    // 进入睡眠时顺手释放 renderLists，并安排后台缓存裁剪。
    if (renderer.renderLists && renderer.renderLists.dispose) renderer.renderLists.dispose();
    scheduleBackgroundCacheTrim();
  }
}
// 安装可见性和焦点监听，把宿主窗口状态变化同步到 CSS、renderer 和视觉恢复逻辑。
function installRenderPowerHooks() {
  updateRenderPowerClasses();
  document.addEventListener('visibilitychange', function(){
    // 页面隐藏/显示时立即更新功耗模式。
    updateRenderPowerClasses();
    applyRendererPowerMode();
    if (!isDeepBackgroundMode()) recoverVisualsAfterBackground('visibilitychange');
  });
  window.addEventListener('focus', function(){
    // 窗口重新聚焦时恢复前台渲染，并触发视觉层恢复。
    desktopRuntimeState.focused = true;
    updateRenderPowerClasses();
    applyRendererPowerMode();
    if (!isDeepBackgroundMode()) recoverVisualsAfterBackground('focus');
  });
  window.addEventListener('blur', function(){
    // 失焦只降低状态，不主动恢复视觉。
    desktopRuntimeState.focused = false;
    updateRenderPowerClasses();
    applyRendererPowerMode();
  });
}



// ===== js/01-scene-camera-input.js =====

// ============================================================
//  Three.js 场景
// ============================================================
// 主 Three.js 场景，所有粒子、歌词、歌单架和辅助层最终都挂到这里。
var scene = new THREE.Scene();
// 背景保持透明，由 DOM 背景和封面背景层负责呈现。
scene.background = null;
// 主透视相机，默认 45 度视野，后续由轨道相机、电影镜头或自由相机驱动。
var camera = new THREE.PerspectiveCamera(45, innerWidth / innerHeight, 0.1, 100);
// 前台渲染 DPR 上限，防止高 DPI 屏幕带来过高像素成本。
var RENDER_DPR_CAP = 1.35;
// 前台渲染像素预算，实际 DPR 会按窗口面积动态下调。
var RENDER_PIXEL_BUDGET = 5200000;
// 前台最低 DPR，保证省电时仍保留基本清晰度。
var RENDER_MIN_DPR = 0.72;
// 0 = display vsync. Keep visible playback high-refresh capable instead of capping 120Hz+ screens to 60/72.
// 可见播放时是否跟随显示器 vsync；true 表示不主动限帧。
var RENDER_VISIBLE_VSYNC = true;
// 普通前台目标帧率，0 表示不限制。
var RENDER_ACTIVE_FPS = 0;
// 大视口前台目标帧率，0 表示不限制。
var RENDER_LARGE_FPS = 0;
// 超大视口前台目标帧率，0 表示不限制。
var RENDER_HUGE_FPS = 0;
// 交互期间普通视口目标帧率，0 表示不限制。
var RENDER_INTERACTION_FPS = 0;
// 交互期间大视口目标帧率，0 表示不限制。
var RENDER_INTERACTION_LARGE_FPS = 0;
// 交互期间超大视口目标帧率，0 表示不限制。
var RENDER_INTERACTION_HUGE_FPS = 0;
// 一次交互后保持提帧的时长。
var RENDER_INTERACTION_HOLD_MS = 900;
// 交互提帧截止时间戳。
var renderInteractionBoostUntil = 0;
// 最近一次触发交互提帧的原因，供性能快照诊断。
var renderInteractionReason = '';
// 根据用户选择的质量档位返回 DPR 上限、下限和像素预算。
function renderQualityProfile() {
  // 档位来自视觉控制台，normalizePerformanceQuality 负责兼容非法值。
  var quality = normalizePerformanceQuality(fx && fx.performanceQuality);
  // 省电档位降低 DPR 和像素预算。
  if (quality === 'eco') return { cap: 0.95, min: 0.56, budget: 2400000 };
  // 平衡档位介于省电和高质量之间。
  if (quality === 'balanced') return { cap: 1.12, min: 0.66, budget: 3800000 };
  // 超高档位允许更高 DPR 和像素预算。
  if (quality === 'ultra') return { cap: 1.75, min: 0.85, budget: 7800000 };
  // 默认高质量档位使用全局默认预算。
  return { cap: RENDER_DPR_CAP, min: RENDER_MIN_DPR, budget: RENDER_PIXEL_BUDGET };
}
// 计算当前 renderer 应使用的 DPR。
function getRenderPixelRatio() {
  // 基础 DPR 来自设备像素比。
  var device = window.devicePixelRatio || 1;
  // 深度后台模式强制压低 DPR。
  if (isDeepBackgroundMode()) return Math.min(device, 0.30);
  // 按 CSS 像素面积和预算反推最大 DPR。
  var cssPixels = Math.max(1, innerWidth * innerHeight);
  var quality = renderQualityProfile();
  var budgetCap = Math.sqrt(quality.budget / cssPixels);
  // DPR 同时受质量档位 cap 和像素预算 cap 限制。
  var cap = Math.min(quality.cap, budgetCap);
  return Math.max(quality.min, Math.min(device, cap));
}
// 计算当前理论渲染像素数，用于判断负载档位。
function getRenderPixelLoad() {
  var ratio = getRenderPixelRatio();
  return Math.max(1, innerWidth * innerHeight) * ratio * ratio;
}
// 标记一段用户交互，主循环可以据此临时提高渲染活跃度。
function markRenderInteraction(reason, holdMs) {
  // 后台深度睡眠时不提帧，避免隐藏窗口被交互标记唤醒。
  if (isDeepBackgroundMode()) return;
  var now = performance.now();
  // 多次交互取更晚的截止时间。
  renderInteractionBoostUntil = Math.max(renderInteractionBoostUntil, now + (holdMs || RENDER_INTERACTION_HOLD_MS));
  renderInteractionReason = reason || renderInteractionReason || 'interaction';
  // 立即允许下一帧渲染，避免限帧模式下交互反馈延迟。
  if (typeof renderPerfState !== 'undefined' && renderPerfState) renderPerfState.lastRenderAt = 0;
}
// 判断当前是否仍处于交互提帧窗口。
function isRenderInteractionActive(now) {
  return (now || performance.now()) < renderInteractionBoostUntil;
}
// 根据窗口面积和实际渲染像素量给当前负载分档。
function getRenderLoadTier() {
  // cssPixels 表示布局面积，renderPixels 表示乘上 DPR 后的实际像素量。
  var cssPixels = Math.max(1, innerWidth * innerHeight);
  var renderPixels = (typeof getRenderPixelLoad === 'function') ? getRenderPixelLoad() : cssPixels;
  // 2 表示超大负载，1 表示大负载，0 表示普通负载。
  if (cssPixels >= 7200000 || renderPixels >= 5000000) return 2;
  if (cssPixels >= 3200000 || renderPixels >= 3600000) return 1;
  return 0;
}
// WebGL 渲染器；关闭抗锯齿以减少粒子场景的成本，透明背景用于叠加 DOM 背景层。
var renderer = new THREE.WebGLRenderer({ antialias: false, alpha: true, powerPreference: 'high-performance' });
// 清屏颜色透明，避免覆盖 album-bg 等 DOM 背景。
renderer.setClearColor(0x000000, 0);
// 初始 DPR 和尺寸使用当前质量策略，后续 resize/后台状态会重新应用。
renderer.setPixelRatio(getRenderPixelRatio());
renderer.setSize(innerWidth, innerHeight);
// canvas 样式保持全屏透明块元素。
renderer.domElement.style.background = 'transparent';
renderer.domElement.style.display = 'block';
renderer.domElement.style.width = '100%';
renderer.domElement.style.height = '100%';
// 允许 canvas 接收焦点，便于后续键盘/指针交互。
renderer.domElement.tabIndex = 0;
// 把 WebGL canvas 挂到页面容器。
document.getElementById('canvas-container').appendChild(renderer.domElement);

// ============================================================
//  相机系统 v7.1 — 分离 user offset / cinema offset
//   - userOrbit: 用户拖拽的目标 (永久保留, 不会被电影模式覆盖)
//   - cinemaOffset: 电影模式的微偏移 (始终叠加, 即使用户在拖)
//   - 最终 theta = userOrbit.theta + cinemaOffset.theta
//   - 回正按钮 / 双击屏幕: 让 userOrbit 缓慢归零
// ============================================================
// 轨道相机状态：用户旋转、电影镜头偏移、焦点跟随和发光跟随都汇总在这个对象里。
var orbit = {
  userTheta: 0.0, userPhi: 0.08, userRadius: 6.6,
  cineTheta: 0.0, cinePhi: 0.0, cineRadius: 0.0,
  theta: 0.0, phi: 0.08, radius: 6.6,
  minPhi: -Math.PI*0.45, maxPhi: Math.PI*0.45,
  minRadius: 2.4, maxRadius: 14.0,
  baselineTheta: 0.0, baselinePhi: 0.08, baselineRadius: 6.6,
  rotating: false, last:{x:0,y:0},
  recentering: false,
  centerLocked: false,
  // v8: 镜头跟拍 (hover shelf / queue 时)
  lookAt: new THREE.Vector3(0,0,0),
  focus: {
    active: false,
    type: null,        // 'shelf-side' | 'shelf-stage' | 'queue'
    theta: 0.0, phi: 0.08, radius: 6.6,
    lookAt: new THREE.Vector3(0,0,0),
  },
  glowFollowX: 0,
  glowFollowY: 0,
  glowFollowRoll: 0,
  beatGlow: 0,
};
// 复用的零向量，避免热点路径重复分配。
var ZERO_VEC = new THREE.Vector3(0,0,0);
// 默认相机视野角。
var BASE_FOV = 45;
// 节拍镜头冲击强度。
var camPunch = 0;
// 电影镜头内部时间，用于持续微动。
var cinemaT = 0;
// 创建自由相机默认状态。
function defaultFreeCameraState() {
  return {
    // active 表示当前由自由相机接管主相机。
    active: false,
    // locked 表示保存了自由相机状态但不一定正在激活。
    locked: false,
    position: new THREE.Vector3(0, 0, 6.6),
    yaw: 0,
    pitch: 0,
    roll: 0,
    fov: BASE_FOV,
    velocity: new THREE.Vector3(),
    keys: {},
    resetTween: null
  };
}
// 从本地存储读取自由相机状态，并对位置、角度和 FOV 做范围限制。
function readFreeCameraState() {
  // 先创建默认值，读取失败时直接返回默认状态。
  var state = defaultFreeCameraState();
  try {
    // 存档结构可能来自旧版本，所有字段都逐项保护。
    var raw = JSON.parse(localStorage.getItem(FREE_CAMERA_STORE_KEY) || '{}') || {};
    if (raw.position) {
      // 位置限制在合理范围内，避免错误存档把相机丢到不可见区域。
      state.position.set(
        clampRange(Number(raw.position.x) || 0, -80, 80),
        clampRange(Number(raw.position.y) || 0, -80, 80),
        clampRange(Number(raw.position.z) || 6.6, -80, 80)
      );
    }
    state.yaw = clampRange(Number(raw.yaw) || 0, -Math.PI * 8, Math.PI * 8);
    // pitch 限制在接近上下 90 度以内，避免万向节极端状态。
    state.pitch = clampRange(Number(raw.pitch) || 0, -Math.PI * 0.49, Math.PI * 0.49);
    state.roll = clampRange(Number(raw.roll) || 0, -Math.PI, Math.PI);
    state.fov = clampRange(Number(raw.fov) || BASE_FOV, 26, 72);
    // 旧版本可能保存 active，这里只恢复 locked，不在启动时直接进入自由相机。
    state.locked = !!(raw.locked || raw.active);
    state.active = false;
  } catch (e) {}
  return state;
}
// 当前自由相机状态。
var freeCamera = readFreeCameraState();
// 自由相机移动方向临时向量。
var FREE_CAMERA_MOVE = new THREE.Vector3();
// 自由相机目标速度临时向量。
var FREE_CAMERA_TARGET_VEL = new THREE.Vector3();
// 自由相机震动方向临时向量。
var FREE_CAMERA_SHAKE_DIR = new THREE.Vector3();
// 自由相机欧拉角复用对象，使用 YXZ 顺序适配 yaw/pitch/roll。
var FREE_CAMERA_EULER = new THREE.Euler(0, 0, 0, 'YXZ');
// 重置自由相机时用到的 lookAt 矩阵。
var FREE_CAMERA_RESET_MAT = new THREE.Matrix4();
// 重置自由相机时用到的旋转四元数。
var FREE_CAMERA_RESET_QUAT = new THREE.Quaternion();
// 自由相机世界上方向。
var FREE_CAMERA_UP = new THREE.Vector3(0, 1, 0);
// 自由相机指针输入状态。
var freeCameraPointer = { seen: false, x: 0, y: 0 };
// 自由相机延迟保存计时器。
var freeCameraDeferredSaveTimer = 0;
// 保存自由相机状态到本地存储。
function saveFreeCameraState() {
  // 状态未初始化时无需保存。
  if (!freeCamera) return;
  try {
    // 只保存可序列化的基础字段，Vector3 拆成普通对象。
    localStorage.setItem(FREE_CAMERA_STORE_KEY, JSON.stringify({
      locked: !!freeCamera.locked,
      active: !!freeCamera.active,
      position: { x: freeCamera.position.x, y: freeCamera.position.y, z: freeCamera.position.z },
      yaw: freeCamera.yaw,
      pitch: freeCamera.pitch,
      roll: freeCamera.roll,
      fov: freeCamera.fov
    }));
  } catch (e) {}
}
// 延迟保存自由相机状态，避免拖拽或连续按键时频繁写 localStorage。
function scheduleFreeCameraStateSave(delay) {
  // 已经有等待中的保存任务时不重复排队。
  if (freeCameraDeferredSaveTimer) return;
  freeCameraDeferredSaveTimer = setTimeout(function(){
    freeCameraDeferredSaveTimer = 0;
    saveFreeCameraState();
  }, delay || 720);
}
// 三次缓出曲线，输入会先限制到 0..1。
function easeOutCubic01(t) {
  t = clamp01(t);
  return 1 - Math.pow(1 - t, 3);
}
// 计算从 from 到 to 的最短角度差，处理跨越 -π/π 的情况。
function shortestAngleDelta(from, to) {
  return Math.atan2(Math.sin(to - from), Math.cos(to - from));
}
// 获取自由相机重置目标位姿，骷髅预设下会对齐骷髅专用相机构图。
function getDefaultFreeCameraResetPose() {
  // 默认位姿与普通轨道相机初始构图一致。
  var pose = {
    position: new THREE.Vector3(0, 0, 6.6),
    yaw: 0,
    pitch: 0,
    roll: 0,
    fov: BASE_FOV
  };
  if (typeof SKULL_PRESET_INDEX !== 'undefined' && fx && fx.preset === SKULL_PRESET_INDEX && typeof setSkullCameraTargetVectors === 'function') {
    // 骷髅预设需要从专用目标点反推出 yaw/pitch/roll。
    var look = new THREE.Vector3();
    var shelfComposition = typeof isSkullShelfCompositionActive === 'function' && isSkullShelfCompositionActive();
    setSkullCameraTargetVectors(pose.position, look, innerHeight > innerWidth * 1.08, shelfComposition, 0);
    FREE_CAMERA_RESET_MAT.lookAt(pose.position, look, FREE_CAMERA_UP);
    FREE_CAMERA_RESET_QUAT.setFromRotationMatrix(FREE_CAMERA_RESET_MAT);
    FREE_CAMERA_EULER.setFromQuaternion(FREE_CAMERA_RESET_QUAT, 'YXZ');
    pose.pitch = FREE_CAMERA_EULER.x;
    pose.yaw = FREE_CAMERA_EULER.y;
    pose.roll = FREE_CAMERA_EULER.z;
  }
  return pose;
}
// 把当前主相机位姿捕获到自由相机状态中。
function captureFreeCameraFromCurrent() {
  // 自由相机状态不存在时先补一个默认状态。
  if (!freeCamera) freeCamera = defaultFreeCameraState();
  // 确保相机世界矩阵是最新的，再读取位置和旋转。
  camera.updateMatrixWorld(true);
  freeCamera.position.copy(camera.position);
  FREE_CAMERA_EULER.setFromQuaternion(camera.quaternion, 'YXZ');
  freeCamera.pitch = FREE_CAMERA_EULER.x;
  freeCamera.yaw = FREE_CAMERA_EULER.y;
  freeCamera.roll = FREE_CAMERA_EULER.z;
  freeCamera.fov = clampRange(camera.fov || BASE_FOV, 26, 72);
}
// 如果自由相机处于激活或锁定状态，把自由相机状态应用到主相机。
function applyFreeCameraToCamera() {
  if (!freeCamera || !(freeCamera.active || freeCamera.locked)) return false;
  // 自由相机仍叠加少量电影震动，避免锁定后画面完全静止。
  var cameraShake = clampRange(Number(fx.cinemaShake) || 0, 0, 1.8);
  // 自由相机位置作为基础位置。
  camera.position.copy(freeCamera.position);
  // 使用 YXZ 顺序，保证 yaw/pitch/roll 和保存格式一致。
  camera.rotation.order = 'YXZ';
  camera.rotation.set(
    freeCamera.pitch + beatCam.phiKick * cameraShake * 0.45,
    freeCamera.yaw + beatCam.thetaKick * cameraShake * 0.45,
    freeCamera.roll + beatCam.rollKick * cameraShake
  );
  if (cameraShake > 0 && Math.abs(beatCam.radiusKick) > 0.0001) {
    // 半径方向冲击沿当前相机前向移动，形成节拍推进或回弹感。
    FREE_CAMERA_SHAKE_DIR.set(0, 0, -1).applyEuler(camera.rotation);
    camera.position.addScaledVector(FREE_CAMERA_SHAKE_DIR, beatCam.radiusKick * cameraShake * 0.52);
  }
  // camPunch 和 beatCam.punch 共同影响 FOV，节拍强时略微收窄视野。
  var cameraPunch = Math.max(camPunch * 0.55, beatCam.punch * 0.54 + beatCam.radiusKick * 0.16) * cameraShake;
  var targetFov = clampRange(freeCamera.fov || BASE_FOV, 26, 72) - cameraPunch * 1.75;
  camera.fov += (targetFov - camera.fov) * (targetFov < camera.fov ? 0.24 : 0.12);
  camera.updateProjectionMatrix();
  camPunch *= 0.86;
  return true;
}
// 更新自由相机提示条显示状态。
function updateFreeCameraHint() {
  var el = document.getElementById('free-camera-hint');
  if (el) el.classList.toggle('show', !!(freeCamera && freeCamera.active));
}
// 将自由相机平滑重置到默认构图。
function resetFreeCameraToDefault() {
  // 未初始化自由相机时无需处理。
  if (!freeCamera) return;
  if (freeCameraDeferredSaveTimer) {
    // 重置前取消延迟保存，避免旧位置在动画中途写回。
    clearTimeout(freeCameraDeferredSaveTimer);
    freeCameraDeferredSaveTimer = 0;
  }
  // 保存当前位姿作为重置动画起点。
  var fromPos = freeCamera.position ? freeCamera.position.clone() : new THREE.Vector3(0, 0, 6.6);
  // 根据当前预设得到目标位姿。
  var resetPose = getDefaultFreeCameraResetPose();
  // resetTween 由 updateFreeCamera 每帧消费。
  freeCamera.resetTween = {
    start: performance.now(),
    duration: 620,
    from: {
      position: fromPos,
      yaw: Number(freeCamera.yaw) || 0,
      pitch: Number(freeCamera.pitch) || 0,
      roll: Number(freeCamera.roll) || 0,
      fov: Number(freeCamera.fov) || BASE_FOV
    },
    to: {
      position: resetPose.position,
      yaw: resetPose.yaw,
      pitch: resetPose.pitch,
      roll: resetPose.roll,
      fov: resetPose.fov
    }
  };
  // 重置动画期间不接受自由相机主动移动，但保持 locked 以继续接管相机。
  freeCamera.active = false;
  freeCamera.locked = true;
  // 清空按键和速度，避免动画结束后继续移动。
  freeCamera.keys = {};
  if (freeCamera.velocity) freeCamera.velocity.set(0, 0, 0);
  try { if (document.pointerLockElement === renderer.domElement) document.exitPointerLock(); } catch (e) {}
  updateFreeCameraHint();
  showToast('自由镜头正在平滑回正');
}
// 切换自由相机模式：激活时从当前主相机捕获位姿，关闭时固定当前位置。
function toggleFreeCamera() {
  if (!freeCamera) freeCamera = defaultFreeCameraState();
  if (freeCamera.active) {
    // 再次切换时退出主动移动，但保留 locked，画面停在当前位置。
    freeCamera.active = false;
    freeCamera.locked = true;
    freeCamera.keys = {};
    if (freeCamera.velocity) freeCamera.velocity.set(0, 0, 0);
    try { if (document.pointerLockElement === renderer.domElement) document.exitPointerLock(); } catch (e) {}
    saveFreeCameraState();
    updateFreeCameraHint();
    showToast('自由镜头已固定');
    return;
  }
  // 开启时以当前相机位置为起点，避免画面跳变。
  captureFreeCameraFromCurrent();
  freeCamera.active = true;
  freeCamera.locked = true;
  freeCamera.resetTween = null;
  freeCamera.keys = {};
  freeCameraPointer.seen = false;
  if (!freeCamera.velocity) freeCamera.velocity = new THREE.Vector3();
  try { renderer.domElement.focus && renderer.domElement.focus({ preventScroll: true }); } catch (e) {
    // 旧浏览器不支持 preventScroll 时降级为普通 focus。
    try { renderer.domElement.focus && renderer.domElement.focus(); } catch (ignore) {}
  }
  saveFreeCameraState();
  updateFreeCameraHint();
  try {
    // 指针锁定让鼠标移动可以持续控制相机视角。
    var lockResult = renderer.domElement.requestPointerLock && renderer.domElement.requestPointerLock();
    if (lockResult && lockResult.catch) lockResult.catch(function(){ freeCameraPointer.seen = false; });
  } catch (e) {
    freeCameraPointer.seen = false;
  }
  showToast('自由镜头: WASD 移动 · 鼠标转向 · K 回正');
}
// 每帧更新自由相机位置、重置动画和键盘移动。
function updateFreeCamera(dt) {
  if (!freeCamera) return;
  if (freeCamera.resetTween) {
    // 正在执行回正动画时，按缓出曲线插值位置、角度和 FOV。
    var tw = freeCamera.resetTween;
    var t = easeOutCubic01((performance.now() - tw.start) / Math.max(1, tw.duration || 620));
    freeCamera.position.copy(tw.from.position).lerp(tw.to.position, t);
    freeCamera.yaw = tw.from.yaw + shortestAngleDelta(tw.from.yaw, tw.to.yaw) * t;
    freeCamera.pitch = tw.from.pitch + (tw.to.pitch - tw.from.pitch) * t;
    freeCamera.roll = tw.from.roll + shortestAngleDelta(tw.from.roll, tw.to.roll) * t;
    freeCamera.fov = tw.from.fov + (tw.to.fov - tw.from.fov) * t;
    if (t >= 0.999) {
      // 动画结束后写入精确目标值，并释放自由相机接管。
      freeCamera.position.copy(tw.to.position);
      freeCamera.yaw = tw.to.yaw;
      freeCamera.pitch = tw.to.pitch;
      freeCamera.roll = tw.to.roll;
      freeCamera.fov = tw.to.fov;
      freeCamera.resetTween = null;
      freeCamera.active = false;
      freeCamera.locked = false;
      saveFreeCameraState();
      updateFreeCameraHint();
      recenterCamera();
      showToast('自由镜头已回正');
    }
    return;
  }
  // 未激活时只保留 locked 应用，不处理键盘移动。
  if (!freeCamera.active) return;
  // keys 由键盘事件维护，这里只把按键状态转换为移动向量。
  var keys = freeCamera.keys || {};
  FREE_CAMERA_MOVE.set(0, 0, 0);
  if (keys.KeyW) FREE_CAMERA_MOVE.z -= 1;
  if (keys.KeyS) FREE_CAMERA_MOVE.z += 1;
  if (keys.KeyA) FREE_CAMERA_MOVE.x -= 1;
  if (keys.KeyD) FREE_CAMERA_MOVE.x += 1;
  if (keys.Space) FREE_CAMERA_MOVE.y += 1;
  if (keys.ControlLeft || keys.ControlRight) FREE_CAMERA_MOVE.y -= 1;
  if (!freeCamera.velocity) freeCamera.velocity = new THREE.Vector3();
  var targetVel = FREE_CAMERA_TARGET_VEL.set(0, 0, 0);
  if (FREE_CAMERA_MOVE.lengthSq() > 0) {
    // 归一化后按当前 yaw/pitch 旋转到世界方向。
    FREE_CAMERA_MOVE.normalize();
    FREE_CAMERA_EULER.set(freeCamera.pitch, freeCamera.yaw, 0, 'YXZ');
    FREE_CAMERA_MOVE.applyEuler(FREE_CAMERA_EULER);
    var speed = (keys.ShiftLeft || keys.ShiftRight ? 6.2 : 2.35);
    targetVel.copy(FREE_CAMERA_MOVE).multiplyScalar(speed);
  }
  // 有输入时加速较慢，松手时阻尼更快，手感更稳。
  var ease = targetVel.lengthSq() > 0 ? 8.2 : 13.5;
  freeCamera.velocity.lerp(targetVel, clampRange(ease * Math.max(0.001, dt || 1 / 60), 0, 1));
  if (freeCamera.velocity.lengthSq() < 0.0004) freeCamera.velocity.set(0, 0, 0);
  freeCamera.position.addScaledVector(freeCamera.velocity, Math.max(0.001, dt || 1 / 60));
  // Q/E 控制 roll，限制在 -π..π。
  var rollDir = (keys.KeyQ ? 1 : 0) - (keys.KeyE ? 1 : 0);
  if (rollDir) freeCamera.roll = clampRange(freeCamera.roll + rollDir * dt * 0.9, -Math.PI, Math.PI);
  scheduleFreeCameraStateSave(720);
}
// 页面卸载或隐藏前持久化视觉设置和自由相机状态。
function flushPersistentVisualState() {
  try { saveLyricLayout(); } catch (e) {}
  try { saveFreeCameraState(); } catch (e) {}
}
// beforeunload 和 pagehide 都注册保存，覆盖普通关闭、路由切换和移动端页面冻结。
window.addEventListener('beforeunload', flushPersistentVisualState);
window.addEventListener('pagehide', flushPersistentVisualState);

// 重置节拍镜头同步状态，通常在切歌、seek 或重新对齐 beatMap 时调用。
function resetBeatCameraSync(t) {
  // 清空预解析节拍队列和当前冲击包络。
  beatCam.nextIdx = 0;
  beatCam.events.length = 0;
  beatCam.punch = 0;
  beatCam.lastTriggerAt = -10;
  beatCam.lastRealtimeAt = -10;
  beatCam.thetaKick = 0;
  beatCam.phiKick = 0;
  beatCam.radiusKick = 0;
  beatCam.rollKick = 0;
  beatCam.prevAudioTime = isFinite(t) ? t : -1;
  camPunch = 0;
  // 统计归零，避免跨歌曲累积。
  beatCam.stats.map = 0;
  beatCam.stats.live = 0;
  beatCam.stats.merged = 0;
  beatCam.stats.liveBlocked = 0;
  liveCamAvg = 0;
  liveCamPeak = 0.28;
  liveCamLastRaw = 0;
  resetRealtimeBeatEngine();
}

// 把节拍镜头游标同步到指定播放时间。
function syncBeatCameraToTime(t) {
  resetBeatCameraSync(t);
  // 没有当前 beatMap 时只做状态重置。
  if (!currentBeatMap) return;
  alignBeatCameraCursorToTime(t);
}

// 将 beatCam.nextIdx 前移到当前时间之后的第一个可预判节拍。
function alignBeatCameraCursorToTime(t) {
  if (!currentBeatMap) return;
  // 兼容不同 beatMap 字段命名。
  var beats = currentBeatMap.cameraBeats || currentBeatMap.beats || currentBeatMap.kicks || [];
  beatCam.nextIdx = 0;
  while (beatCam.nextIdx < beats.length) {
    // beat 项既可能是数字，也可能是 { time } 对象。
    var bt = typeof beats[beatCam.nextIdx] === 'number' ? beats[beatCam.nextIdx] : beats[beatCam.nextIdx].time;
    if (bt >= t + beatCam.lookahead) break;
    beatCam.nextIdx++;
  }
}

// 节拍镜头使用的 smoothstep 缓动。
function easeBeatCamera(x) {
  x = Math.max(0, Math.min(1, x));
  return x * x * (3 - 2 * x);
}

// 根据当前原始能量和低频能量更新电影镜头动态缩放。
function updateCinemaDynamics(rawEnergy, rawLow) {
  // 输入归一化，避免异常频谱值污染长期包络。
  var e = clamp01(rawEnergy || 0);
  var l = clamp01(rawLow || 0);
  var isDj = djMode.active;
  // DJ 模式更重视低频，普通模式更重视总能量。
  var composite = clamp01(e * (isDj ? 0.52 : 0.62) + l * (isDj ? 0.48 : 0.38));
  if (isDj) {
    // DJ 模式额外跟踪段落能量变化，用于更明显的镜头跃迁。
    var prevEnergy = djMode.sectionEnergy || 0;
    var prevLow = djMode.sectionLow || 0;
    djMode.sectionEnergy += (e - djMode.sectionEnergy) * (e > djMode.sectionEnergy ? 0.030 : 0.010);
    djMode.sectionLow += (l - djMode.sectionLow) * (l > djMode.sectionLow ? 0.036 : 0.012);
    var change = Math.abs(e - prevEnergy) * 0.46 + Math.abs(l - prevLow) * 0.62;
    djMode.sectionChange += (change - djMode.sectionChange) * (change > djMode.sectionChange ? 0.055 : 0.018);
    djMode.visualPulse *= Math.pow(0.30, 1 / 60);
  }
  // avg/lowAvg/peak 是慢速自适应基线，避免不同歌曲音量差异过大。
  cinemaDynamics.avg += (composite - cinemaDynamics.avg) * (composite > cinemaDynamics.avg ? (isDj ? 0.018 : 0.010) : (isDj ? 0.006 : 0.004));
  cinemaDynamics.lowAvg += (l - cinemaDynamics.lowAvg) * (l > cinemaDynamics.lowAvg ? (isDj ? 0.022 : 0.012) : (isDj ? 0.007 : 0.005));
  cinemaDynamics.peak = Math.max(isDj ? 0.36 : 0.30, cinemaDynamics.peak * (isDj ? 0.9980 : 0.9988), composite);
  var floor = Math.max(0.10, cinemaDynamics.avg * 0.82);
  var span = Math.max(0.18, cinemaDynamics.peak - floor);
  // lift 表示当前能量相对基线的抬升程度。
  var lift = clamp01((composite - floor) / span);
  lift = lift * lift * (3 - 2 * lift);
  var target = isDj
    ? 0.50 + lift * 0.66 + clamp01((l - cinemaDynamics.lowAvg) / 0.30) * 0.18 + clamp01(djMode.sectionChange * 2.4) * 0.08
    : 0.42 + lift * 0.56 + clamp01((l - cinemaDynamics.lowAvg) / 0.36) * 0.12;
  if (cinemaDynamics.avg < 0.18 && l < 0.32) target *= isDj ? 0.88 : 0.78;
  if (e > 0.48 && l > 0.46) target = Math.max(target, isDj ? 1.02 : 0.92);
  target = clampRange(target, isDj ? 0.42 : 0.34, isDj ? 1.24 : 1.08);
  // 目标变大时快跟随，变小时慢回落，形成更自然的电影镜头呼吸。
  cinemaDynamics.scale += (target - cinemaDynamics.scale) * (target > cinemaDynamics.scale ? (isDj ? 0.070 : 0.045) : (isDj ? 0.030 : 0.022));
}

// 组合电影镜头动态、歌曲画像和 DJ 加成，得到最终镜头强度倍率。
function cameraDynamicsScale(extra) {
  var isDj = djMode.active;
  // DJ 模式下按低频段落和 tempo 置信度加一点镜头强度。
  var djBoost = isDj ? (1.06 + clamp01(djMode.sectionLow) * 0.16 + clamp01(rtBeat.tempoConfidence) * 0.08) : 1;
  return clampRange((cinemaDynamics.scale || 0.82) * (cinemaTrackProfile.scale || 1) * (extra == null ? 1 : extra) * djBoost, isDj ? 0.24 : 0.18, isDj ? 1.42 : 1.18);
}

// 根据歌曲名/歌手名提供少量人工镜头强度提示，用于已知歌曲的特殊调校。
function cinemaTrackNameHint(song) {
  var label = ((song && song.name) || '') + ' ' + ((song && song.artist) || '');
  label = label.toLowerCase().replace(/\s+/g, '');
  if (/after17/.test(label)) return 0.46;
  if (/joey/.test(label)) return 1.08;
  return 1.0;
}

// 根据歌曲标题和歌手返回分析策略画像，某些歌曲使用更柔和或更稀疏的镜头策略。
function cinemaAnalysisProfileForSong(song) {
  // 标题和歌手统一小写并去空白，便于中英文规则匹配。
  var title = String((song && (song.name || song.title)) || '').toLowerCase().replace(/\s+/g, '');
  var artist = String((song && song.artist) || '').toLowerCase().replace(/\s+/g, '');
  var label = title + ' ' + artist;
  if (/日落大道|sunsetboulevard/.test(label)) {
    // 日落大道类曲目使用柔和律动和稀疏镜头，避免过强节拍切换。
    return {
      id: 'sunset-boulevard-soft-groove',
      softGroove: true,
      phaseScan: true,
      localRefine: true,
      sparseCamera: true,
      introPattern: true
    };
  }
  return { id: 'default', softGroove: false, phaseScan: false, localRefine: false, sparseCamera: false, introPattern: false };
}

// 重置当前歌曲的电影镜头画像统计。
function resetCinemaTrackProfile(song) {
  // scale/target 先回到中性，后续由频谱逐帧学习。
  cinemaTrackProfile.scale = 1.0;
  cinemaTrackProfile.target = 1.0;
  cinemaTrackProfile.nameHint = cinemaTrackNameHint(song);
  cinemaTrackProfile.frames = 0;
  cinemaTrackProfile.energyAvg = 0;
  cinemaTrackProfile.lowAvg = 0;
  cinemaTrackProfile.vocalAvg = 0;
  cinemaTrackProfile.melodyAvg = 0;
  cinemaTrackProfile.punchPeak = 0.10;
  cinemaTrackProfile.density = 0;
}

// 用实时频谱样本持续更新当前歌曲的电影镜头画像。
function updateCinemaTrackProfile(sample) {
  if (!sample) return;
  // p 是 cinemaTrackProfile 的局部别名，便于下面多次读写。
  var p = cinemaTrackProfile;
  p.frames++;
  // 简单一阶跟随函数，用于平滑各类长期均值。
  function follow(cur, next, k) { return cur + (next - cur) * k; }
  // 前几秒学习速度更快，后面改为慢速适应。
  var early = p.frames < 360;
  var k = early ? 0.020 : 0.006;
  // 分别学习总能量、低频、人声和旋律平均值。
  p.energyAvg = follow(p.energyAvg, clamp01(sample.energy), k);
  p.lowAvg = follow(p.lowAvg, clamp01(sample.low), k);
  p.vocalAvg = follow(p.vocalAvg, clamp01(sample.vocal), k * 0.8);
  p.melodyAvg = follow(p.melodyAvg, clamp01(sample.melody), k * 0.8);
  // punchRaw 代表瞬态冲击感，低频上升沿权重最高。
  var punchRaw = clamp01((sample.lowOnset || 0) * 2.4 + (sample.energyOnset || 0) * 1.5 + sample.low * 0.16);
  p.punchPeak = Math.max(0.10, p.punchPeak * 0.9975, punchRaw);
  // 下面把长期画像拆成低频驱动、响度驱动、冲击驱动、人声柔化和安静柔化。
  var lowDrive = clamp01((p.lowAvg - 0.20) / 0.42);
  var loudDrive = clamp01((p.energyAvg - 0.18) / 0.40);
  var punchDrive = clamp01((p.punchPeak - 0.13) / 0.36);
  var vocalSoft = clamp01((p.vocalAvg * 0.72 + p.melodyAvg * 0.42 - p.lowAvg * 0.34 - 0.08) / 0.42);
  var quietSoft = clamp01((0.24 - p.energyAvg) / 0.18);
  // DJ 模式更强调低频和冲击，普通模式会被人声和安静段明显压低。
  var target = djMode.active
    ? 0.72 + lowDrive * 0.34 + loudDrive * 0.18 + punchDrive * 0.42 - vocalSoft * 0.12 - quietSoft * 0.06
    : 0.54 + lowDrive * 0.28 + loudDrive * 0.22 + punchDrive * 0.34 - vocalSoft * 0.34 - quietSoft * 0.18;
  if (p.density) target += clamp01((p.density - 0.55) / 1.6) * 0.14;
  // 已知歌曲名提示作为最后倍率。
  target *= p.nameHint || 1;
  target = clampRange(target, djMode.active ? 0.68 : 0.28, djMode.active ? 1.26 : 1.12);
  p.target = target;
  // 普通模式下降更快，避免柔和歌曲被早期强节拍长期抬高。
  p.scale += (target - p.scale) * (target > p.scale ? (djMode.active ? 0.045 : 0.030) : (djMode.active ? 0.030 : 0.045));
}

// 使用预解析 beatMap 的统计结果修正电影镜头画像。
function applyCinemaProfileFromBeatMap(map) {
  // 没有时长无法计算密度。
  if (!map || !map.duration) return;
  // 只统计可用于相机的非数字事件，过滤掉普通节拍点。
  var events = (map.cameraBeats || map.beats || []).filter(function(b){ return b && typeof b !== 'number' && b.camera !== false; });
  if (!events.length) return;
  // 聚合冲击、低频和 primary 数量。
  var sumImpact = 0, sumLow = 0, primary = 0;
  events.forEach(function(b){
    sumImpact += Math.max(b.impact || 0, b.strength || 0);
    sumLow += b.low || 0;
    if (b.primary !== false) primary++;
  });
  var avgImpact = sumImpact / events.length;
  var avgLow = sumLow / events.length;
  // 密度按每秒相机事件数量估计，分母下限避免短歌或片段过度放大。
  var density = events.length / Math.max(20, map.duration);
  cinemaTrackProfile.density = density;
  var target = 0.44 + clamp01((avgImpact - 0.20) / 0.55) * 0.38 + clamp01((avgLow - 0.24) / 0.48) * 0.18 + clamp01((density - 0.45) / 1.65) * 0.20 + clamp01(primary / Math.max(1, events.length)) * 0.08;
  target *= cinemaTrackProfile.nameHint || 1;
  target = clampRange(target, 0.28, 1.12);
  cinemaTrackProfile.target = target;
  cinemaTrackProfile.scale += (target - cinemaTrackProfile.scale) * (target < cinemaTrackProfile.scale ? 0.55 : 0.22);
}

// 重置实时节拍检测器的全部包络、峰值、节拍间隔和统计。
function resetRealtimeBeatEngine() {
  // 快慢包络全部清零，避免上一首歌的频段状态影响新歌。
  rtBeat.subFast = rtBeat.subSlow = rtBeat.lowFast = rtBeat.lowSlow = 0;
  rtBeat.bodyFast = rtBeat.bodySlow = rtBeat.vocalFast = rtBeat.vocalSlow = rtBeat.snapFast = rtBeat.snapSlow = 0;
  rtBeat.prevSub = rtBeat.prevLow = rtBeat.prevBody = rtBeat.prevVocal = rtBeat.prevSnap = rtBeat.prevRms = 0;
  rtBeat.onsetAvg = 0.012;
  rtBeat.onsetPeak = 0.060;
  rtBeat.subPeak = 0.14;
  rtBeat.lowPeak = 0.18;
  rtBeat.bodyPeak = 0.16;
  rtBeat.vocalPeak = 0.16;
  rtBeat.snapPeak = 0.14;
  rtBeat.lastHitAt = -10;
  rtBeat.tempoGap = 0;
  rtBeat.tempoConfidence = 0;
  rtBeat.beatCount = 0;
  rtBeat.primedFrames = 0;
  // 切歌或 seek 后留出 warmup 时间，避免刚恢复时的瞬态被误判成节拍。
  rtBeat.warmupUntil = (audio && isFinite(audio.currentTime) ? audio.currentTime : 0) + (djMode.active ? 0.34 : 1.15);
  rtBeat.pulse = 0;
  rtBeat.score = 0;
  rtBeat.stats.hits = 0;
  rtBeat.stats.blocked = 0;
  rtBeat.stats.assisted = 0;
  rtBeat.stats.strong = 0;
  rtBeat.stats.rejected = 0;
}

// 重置音频驱动的所有视觉能量状态。
function resetAudioVisualState() {
  // 当前帧能量清零。
  bass = 0;
  mid = 0;
  treble = 0;
  audioEnergy = 0;
  beatPulse = 0;
  prevEnergy = 0;
  smoothBass = 0;
  smoothMid = 0;
  smoothTreb = 0;
  smoothEnergy = 0;
  bassPeak = 0.12;
  midPeak = 0.10;
  treblePeak = 0.08;
  energyPeak = 0.10;
  // 预排节拍脉冲和上升沿状态清零。
  scheduledBeatPulse = 0;
  scheduledBeatFlag = false;
  beatOnsetFlag = false;
  cinemaDynamics.avg = 0;
  cinemaDynamics.lowAvg = 0;
  cinemaDynamics.peak = 0.30;
  cinemaDynamics.scale = 0.82;
  // DJ 模式下同步重置 DJ 量表。
  if (djMode.active) resetDjModeMeter();
}

// 从数字或对象形式的 beat 事件中读取时间。
function beatEventTime(ev) {
  return typeof ev === 'number' ? ev : (ev && isFinite(ev.time) ? ev.time : Infinity);
}

// 让出一次绘制机会，适合在重任务前等待浏览器先刷新 UI。
function yieldToPaint() {
  return new Promise(function(resolve) {
    // 后台或无 RAF 环境下直接用 setTimeout。
    if (isHiddenForBackgroundOptimization() || typeof requestAnimationFrame !== 'function') {
      setTimeout(resolve, 0);
    } else {
      requestAnimationFrame(function(){ setTimeout(resolve, 0); });
    }
  });
}

// 等待浏览器空闲时间，后台时使用短 timeout，避免任务永久挂起。
function yieldToIdle(timeout) {
  return new Promise(function(resolve) {
    // 后台优化状态下不依赖 requestIdleCallback，直接短延迟返回。
    if (isHiddenForBackgroundOptimization()) {
      setTimeout(resolve, Math.min(timeout || 80, 80));
      return;
    }
    // 优先使用 requestIdleCallback，把非关键视觉任务让给交互和渲染。
    if (typeof requestIdleCallback === 'function') {
      requestIdleCallback(function(){ resolve(); }, { timeout: timeout || 1200 });
    } else {
      setTimeout(resolve, timeout ? Math.min(timeout, 600) : 160);
    }
  });
}

// 延迟并在空闲帧执行视觉应用任务，常用于封面、AI 深度和重建类操作。
function scheduleVisualApply(fn, delay, timeout) {
  if (typeof fn !== 'function') return;
  setTimeout(function(){
    // 后台时直接执行，避免等待不可见页面的 RAF。
    if (isHiddenForBackgroundOptimization() || typeof requestAnimationFrame !== 'function') {
      fn();
      return;
    }
    // 空闲后再进下一帧，减少和当前帧绘制竞争。
    var run = function(){ requestAnimationFrame(fn); };
    if (window.requestIdleCallback) requestIdleCallback(run, { timeout: timeout || 360 });
    else run();
  }, delay || 0);
}

// 安排 UI 预热任务，例如纹理上传、控制条位移图刷新等。
function scheduleUiWarmTask(fn, timeout) {
  if (typeof fn !== 'function') return;
  // 前台优先走 idle + RAF，后台降级为 timeout。
  var run = function(){ requestAnimationFrame(fn); };
  if (isHiddenForBackgroundOptimization() || typeof requestAnimationFrame !== 'function') {
    setTimeout(fn, 0);
  } else if (window.requestIdleCallback) {
    requestIdleCallback(run, { timeout: timeout || 220 });
  } else {
    requestAnimationFrame(fn);
  }
}

// 取消普通 beatMap 分析计时器。
function cancelBeatAnalysisTimer() {
  if (beatAnalysisTimer) {
    clearTimeout(beatAnalysisTimer);
    beatAnalysisTimer = null;
  }
}

// 计算频谱数组在指定频段内的 RMS 能量。
function beatBandRms(data, sampleRate, fftSize, hz0, hz1) {
  // binHz 表示每个 FFT bin 对应的频率宽度。
  var binHz = sampleRate / fftSize;
  // 频段上下界转换为 bin 索引，并限制在数组范围内。
  var a = Math.max(1, Math.floor(hz0 / binHz));
  var b = Math.min(data.length - 1, Math.ceil(hz1 / binHz));
  var sum = 0, count = 0;
  for (var i = a; i <= b; i++) {
    // 宿主频谱已经映射到 0..255，这里还原到 0..1 后平方累加。
    var v = data[i] / 255;
    sum += v * v;
    count++;
  }
  return count ? Math.sqrt(sum / count) : 0;
}

// 判断输入是否是可按数组读取的宿主频谱数据。
function isHostSpectrumArray(value) {
  return !!(value && typeof value.length === 'number' && (Array.isArray(value) || (typeof ArrayBuffer !== 'undefined' && ArrayBuffer.isView && ArrayBuffer.isView(value))));
}

// 判断当前是否有仍然有效的宿主频谱帧。
function hasHostSpectrumFrame() {
  // 没有时间戳说明从未收到过宿主频谱。
  if (!hostSpectrumFrame || !hostSpectrumFrame.updatedAt) return false;
  var now = (typeof performance !== 'undefined' && performance.now) ? performance.now() : Date.now();
  // 超过 TTL 的频谱视为过期，避免暂停后残留能量。
  if (now - hostSpectrumFrame.updatedAt > HOST_SPECTRUM_TTL_MS) return false;
  return !!(
    ((isHostSpectrumArray(hostSpectrumFrame.bins) && hostSpectrumFrame.bins.length) ||
      (isHostSpectrumArray(hostSpectrumFrame.waveform) && hostSpectrumFrame.waveform.length) ||
      Number(hostSpectrumFrame.rms || 0) > 0 ||
      Number(hostSpectrumFrame.peak || 0) > 0));
}

// 把宿主低维 bins 重采样到旧播放器期望的 frequencyData 长度。
function readHostFrequencyData(target) {
  // 宿主 bins 可能是数组或 TypedArray。
  var bins = hostSpectrumFrame && isHostSpectrumArray(hostSpectrumFrame.bins) ? hostSpectrumFrame.bins : [];
  for (var i = 0; i < target.length; i++) {
    if (!bins.length) {
      target[i] = 0;
      continue;
    }
    // 使用非线性 ratio 让低频获得更多采样密度，适配节拍检测需求。
    var ratio = target.length > 1 ? i / (target.length - 1) : 0;
    var sourceIndex = bins.length > 1 ? Math.min(bins.length - 1, Math.floor(Math.pow(ratio, 0.76) * (bins.length - 1))) : 0;
    target[i] = Math.max(0, Math.min(255, Math.round(clamp01(Number(bins[sourceIndex] || 0)) * 255)));
  }
}

// 把宿主 waveform 重采样到旧播放器期望的 timeDomainData 长度。
function readHostWaveformData(target) {
  var waveform = hostSpectrumFrame && isHostSpectrumArray(hostSpectrumFrame.waveform) ? hostSpectrumFrame.waveform : [];
  for (var i = 0; i < target.length; i++) {
    if (!waveform.length) {
      target[i] = 128;
      continue;
    }
    // waveform 可能是 -1..1 或 0..1，这里统一转到 0..255 的类 AnalyserNode 输出。
    var sourceIndex = Math.min(waveform.length - 1, Math.floor(i / Math.max(1, target.length - 1) * (waveform.length - 1)));
    var value = Number(waveform[sourceIndex] || 0);
    if (value >= 0 && value <= 1) value = value * 2 - 1;
    target[i] = Math.max(0, Math.min(255, Math.round(128 + clampRange(value, -1, 1) * 112)));
  }
}

// 读取宿主 RMS，缺失或非法时使用调用方提供的 fallback。
function readHostSpectrumRms(fallback) {
  var value = Number(hostSpectrumFrame && hostSpectrumFrame.rms);
  return isFinite(value) ? clamp01(value) : (fallback || 0);
}

// 实时节拍检测引擎：从宿主频谱中估计当前帧是否产生可用于镜头和粒子脉冲的 beat。
function processRealtimeBeatEngine(dt) {
  // 没有有效频谱或播放器未播放时不进行实时节拍检测。
  if (!hasHostSpectrumFrame() || !audio || audio.paused) return null;
  // dt 限制在合理范围，避免失焦恢复时的大 dt 破坏包络。
  dt = Math.max(0.001, Math.min(0.080, dt || 0.016));
  var dj = djMode.active;
  // 读取宿主频谱到节拍检测专用缓存。
  readHostFrequencyData(beatFrequencyData);
  readHostWaveformData(beatTimeDomainData);
  // 频段按听感拆成 sub、kick、body、vocal、snap。
  var sr = HOST_SPECTRUM_SAMPLE_RATE;
  var sub = beatBandRms(beatFrequencyData, sr, BEAT_FFT_SIZE, 38, 74);
  var kick = beatBandRms(beatFrequencyData, sr, BEAT_FFT_SIZE, 52, 165);
  var body = beatBandRms(beatFrequencyData, sr, BEAT_FFT_SIZE, 165, 420);
  var vocal = beatBandRms(beatFrequencyData, sr, BEAT_FFT_SIZE, 420, 2600);
  var snap = beatBandRms(beatFrequencyData, sr, BEAT_FFT_SIZE, 1800, 9200);
  var low = Math.min(1, kick * 0.86 + sub * 0.42);
  // 从波形计算 RMS，作为总能量变化的补充。
  var rms = 0;
  for (var i = 0; i < beatTimeDomainData.length; i++) {
    var tv = (beatTimeDomainData[i] - 128) / 128;
    rms += tv * tv;
  }
  rms = Math.sqrt(rms / beatTimeDomainData.length);

  // 指数跟随函数，upTau/downTau 分别控制上升和下降速度。
  function follow(cur, next, upTau, downTau) {
    var tau = next > cur ? upTau : downTau;
    return cur + (next - cur) * (1 - Math.exp(-dt / Math.max(0.001, tau)));
  }
  // DJ 模式下快包络更敏捷，慢包络略慢，便于锁住鼓点。
  var fastMul = dj ? 0.86 : 1;
  var downMul = dj ? 0.94 : 1;
  var slowMul = dj ? 1.06 : 1;
  rtBeat.subFast = follow(rtBeat.subFast, sub, 0.018 * fastMul, 0.064 * downMul);
  rtBeat.subSlow = follow(rtBeat.subSlow, sub, 0.320 * slowMul, 0.520 * slowMul);
  rtBeat.lowFast = follow(rtBeat.lowFast, low, 0.016 * fastMul, 0.070 * downMul);
  rtBeat.lowSlow = follow(rtBeat.lowSlow, low, 0.300 * slowMul, 0.540 * slowMul);
  rtBeat.bodyFast = follow(rtBeat.bodyFast, body, 0.020 * fastMul, 0.082 * downMul);
  rtBeat.bodySlow = follow(rtBeat.bodySlow, body, 0.360 * slowMul, 0.600 * slowMul);
  rtBeat.vocalFast = follow(rtBeat.vocalFast, vocal, 0.026 * fastMul, 0.090 * downMul);
  rtBeat.vocalSlow = follow(rtBeat.vocalSlow, vocal, 0.340 * slowMul, 0.580 * slowMul);
  rtBeat.snapFast = follow(rtBeat.snapFast, snap, 0.012 * fastMul, 0.060 * downMul);
  rtBeat.snapSlow = follow(rtBeat.snapSlow, snap, 0.300 * slowMul, 0.520 * slowMul);

  // 动态峰值用于把当前频段能量归一化，峰值随时间缓慢衰减。
  var peakDecay = dj ? 0.988 : 0.990;
  rtBeat.subPeak = Math.max(rtBeat.subPeak * Math.pow(peakDecay, dt * 60), sub, 0.045);
  rtBeat.lowPeak = Math.max(rtBeat.lowPeak * Math.pow(dj ? 0.987 : 0.989, dt * 60), low, 0.060);
  rtBeat.bodyPeak = Math.max(rtBeat.bodyPeak * Math.pow(peakDecay, dt * 60), body, 0.040);
  rtBeat.vocalPeak = Math.max(rtBeat.vocalPeak * Math.pow(peakDecay, dt * 60), vocal, 0.040);
  rtBeat.snapPeak = Math.max(rtBeat.snapPeak * Math.pow(peakDecay, dt * 60), snap, 0.035);

  // flux 表示原始能量正向变化，rise 表示快慢包络差值，两者共同描述瞬态。
  var subFlux = Math.max(0, sub - rtBeat.prevSub);
  var lowFlux = Math.max(0, low - rtBeat.prevLow);
  var bodyFlux = Math.max(0, body - rtBeat.prevBody);
  var vocalFlux = Math.max(0, vocal - rtBeat.prevVocal);
  var snapFlux = Math.max(0, snap - rtBeat.prevSnap);
  var rmsFlux = Math.max(0, rms - rtBeat.prevRms);
  var subRise = Math.max(0, rtBeat.subFast - rtBeat.subSlow);
  var lowRise = Math.max(0, rtBeat.lowFast - rtBeat.lowSlow);
  var bodyRise = Math.max(0, rtBeat.bodyFast - rtBeat.bodySlow);
  var vocalRise = Math.max(0, rtBeat.vocalFast - rtBeat.vocalSlow);
  var snapRise = Math.max(0, rtBeat.snapFast - rtBeat.snapSlow);
  // 鼓点 onset 以低频为主，音乐性 onset 以中高频和 RMS 为辅。
  var drumOnset = subRise * 0.88 + subFlux * 0.66 + lowRise * 1.62 + lowFlux * 1.34;
  var musicalOnset = bodyRise * 0.34 + bodyFlux * 0.24 + vocalRise * 0.52 + vocalFlux * 0.36 + snapRise * 0.08 + snapFlux * 0.06 + rmsFlux * 0.20;
  var onset = dj ? drumOnset * 1.05 + musicalOnset * 0.07 : drumOnset + musicalOnset * 0.16;

  // onsetAvg/onsetPeak 提供动态阈值，适应不同歌曲响度和密度。
  var avgTau = onset > rtBeat.onsetAvg ? (dj ? 0.88 : 1.10) : (dj ? 0.30 : 0.34);
  rtBeat.onsetAvg = follow(rtBeat.onsetAvg, onset, avgTau, avgTau);
  rtBeat.onsetPeak = Math.max(rtBeat.onsetPeak * Math.pow(dj ? 0.986 : 0.988, dt * 60), onset, 0.032);
  var floor = rtBeat.onsetAvg * (dj ? 0.88 : 0.84);
  var score = clamp01((onset - floor) / Math.max(dj ? 0.013 : 0.014, rtBeat.onsetPeak - floor));
  // 各频段归一化值用于后面的门控判断。
  var subNorm = clamp01(sub / Math.max(0.045, rtBeat.subPeak * (dj ? 0.72 : 0.70)));
  var lowNorm = clamp01(low / Math.max(0.060, rtBeat.lowPeak * (dj ? 0.74 : 0.72)));
  var bodyNorm = clamp01(body / Math.max(0.045, rtBeat.bodyPeak * (dj ? 0.74 : 0.72)));
  var vocalNorm = clamp01(vocal / Math.max(0.045, rtBeat.vocalPeak * 0.72));
  var snapNorm = clamp01(snap / Math.max(0.040, rtBeat.snapPeak * (dj ? 0.78 : 0.72)));
  // 当前音频时间作为节拍间隔和相位判断的基准。
  var nowT = audio.currentTime || 0;
  rtBeat.primedFrames++;
  // warmup 阶段只更新状态，不轻易触发节拍。
  var warmingUp = nowT < rtBeat.warmupUntil || rtBeat.primedFrames < (dj ? 8 : 18);
  var gapFromLast = nowT - rtBeat.lastHitAt;
  // 如果已经估计出 tempoGap，就用相位窗口辅助判断当前帧是否接近预期节拍。
  var expectedGap = rtBeat.tempoGap > 0 ? rtBeat.tempoGap : 0;
  var phaseErr = expectedGap > 0 ? Math.abs(gapFromLast - expectedGap) : 99;
  var phaseWindow = expectedGap > 0 ? Math.max(dj ? 0.055 : 0.055, Math.min(dj ? 0.105 : 0.105, expectedGap * (dj ? 0.16 : 0.16))) : 0;
  var tempoDue = expectedGap > 0 && gapFromLast > expectedGap - phaseWindow && gapFromLast < expectedGap + phaseWindow;
  // 低频存在感、低频攻击性和低频主导度共同决定鼓点可信度。
  var lowPresence = Math.max(lowNorm, subNorm * 0.74);
  var lowAttack = lowRise + lowFlux * 0.72 + subRise * 0.58 + subFlux * 0.40;
  var lowDominance = low / Math.max(0.001, vocal * 0.84 + body * 0.36 + snap * 0.10);
  var lowFluxDominance = (lowFlux + subFlux * 0.58) / Math.max(0.001, vocalFlux * 0.72 + bodyFlux * 0.42 + snapFlux * 0.16);
  // 人声遮罩用于避免强人声瞬态被误判为低频鼓点。
  var voiceMask = dj
    ? (vocalNorm > 0.62 && lowDominance < 0.92 && lowFluxDominance < 1.06 && subNorm < 0.54)
    : (vocalNorm > 0.58 && lowDominance < 0.86 && lowFluxDominance < 1.10);
  var drumGate = lowPresence > (dj ? 0.42 : 0.38) && lowAttack > Math.max(dj ? 0.015 : 0.014, rtBeat.onsetAvg * (dj ? 0.38 : 0.34)) && !voiceMask;
  // 进一步要求低频在响度或通量上占优，降低非鼓点瞬态误触发概率。
  drumGate = drumGate && (lowDominance > (dj ? 0.86 : 0.72) || lowFluxDominance > (dj ? 1.14 : 1.02) || subNorm > (dj ? 0.62 : 0.56));
  // strongTransient 偏保守，kickTransient 偏灵敏，tempoAssist 依赖已锁定节奏的相位窗口。
  var strongTransient = drumGate && score > (dj ? 0.55 : 0.54) && drumOnset > rtBeat.onsetAvg * (dj ? 0.92 : 0.84);
  var kickTransient = drumGate && score > (dj ? 0.43 : 0.40) && lowAttack > Math.max(dj ? 0.020 : 0.018, rtBeat.onsetAvg * (dj ? 0.54 : 0.46));
  var tempoAssist = tempoDue && rtBeat.tempoConfidence > (dj ? 0.40 : 0.42) && drumGate && lowPresence > (dj ? 0.48 : 0) && score > (dj ? 0.30 : 0.22) && lowAttack > Math.max(0.016, rtBeat.onsetAvg * (dj ? 0.44 : 0.34));
  var candidateHit = strongTransient || kickTransient || tempoAssist;
  // 预热阶段不允许触发节拍，只更新检测器内部状态。
  if (warmingUp) candidateHit = false;
  // tempo lock 表示已估计出稳定节拍间隔，后续命中要围绕该间隔验收。
  var hasTempoLock = expectedGap >= (dj ? 0.32 : 0.42) && expectedGap <= (dj ? 0.92 : 0.88) && rtBeat.tempoConfidence > (dj ? 0.36 : 0.38);
  var lockedWindow = hasTempoLock ? Math.max(dj ? 0.062 : 0.070, Math.min(dj ? 0.118 : 0.110, expectedGap * (dj ? 0.17 : 0.16))) : 0;
  var gapRaw = nowT - rtBeat.lastHitAt;
  var rhythmAccept = false;
  if (candidateHit) {
    if (rtBeat.lastHitAt < 0) {
      // 首个命中需要更强的瞬态和低频存在感。
      rhythmAccept = strongTransient && score > (dj ? 0.58 : 0.62) && lowPresence > (dj ? 0.50 : 0.48);
    } else if (hasTempoLock) {
      // 已锁 tempo 后，优先接受一拍误差内或两拍补位的命中。
      var oneBeatErr = Math.abs(gapRaw - expectedGap);
      var twoBeatErr = Math.abs(gapRaw - expectedGap * 2);
      rhythmAccept = oneBeatErr <= lockedWindow && (kickTransient || strongTransient);
      rhythmAccept = rhythmAccept || (twoBeatErr <= lockedWindow * 1.35 && strongTransient && score > (dj ? 0.54 : 0.58));
      rhythmAccept = rhythmAccept || (gapRaw > expectedGap * 1.55 && strongTransient && lowPresence > (dj ? 0.50 : 0.44));
      if (dj) {
        // DJ 模式允许较早的强低频重新校正节奏。
        rhythmAccept = rhythmAccept || (gapRaw > expectedGap * 1.24 && strongTransient && score > 0.56 && lowDominance > 0.92);
      }
    } else {
      // 未锁 tempo 时使用最小间隔和较强瞬态做保守验收。
      rhythmAccept = gapRaw >= (dj ? 0.340 : beatCam.realtimeMinInterval) && strongTransient && score > (dj ? 0.56 : 0.58) && lowPresence > (dj ? 0.50 : 0.44);
    }
  }
  // 最终命中必须同时满足候选和节奏验收。
  var hit = candidateHit && rhythmAccept;
  // 有明显候选但被拒绝时计入 rejected，便于调试阈值。
  if (!hit && (candidateHit || score > 0.42 || vocalNorm > 0.62 || bodyNorm > 0.54)) rtBeat.stats.rejected++;
  // 命中间隔过短则阻止，避免双击鼓点或噪声连续触发。
  var minGap = hasTempoLock ? Math.max(dj ? 0.315 : 0.400, Math.min(dj ? 0.500 : 0.540, expectedGap * (dj ? 0.64 : 0.72))) : (dj ? 0.340 : beatCam.realtimeMinInterval);
  if (hit && gapRaw < minGap) {
    rtBeat.stats.blocked++;
    hit = false;
  }

  // 更新上一帧频段值，供下一帧计算 flux。
  rtBeat.prevSub = sub;
  rtBeat.prevLow = low;
  rtBeat.prevBody = body;
  rtBeat.prevVocal = vocal;
  rtBeat.prevSnap = snap;
  rtBeat.prevRms = rms;
  rtBeat.score = score;
  // 节拍脉冲和 tempo 置信度按时间衰减。
  rtBeat.pulse *= Math.pow(dj ? 0.24 : 0.18, dt);
  rtBeat.tempoConfidence *= Math.pow(dj ? 0.992 : 0.996, dt * 60);

  if (!hit) {
    // 没命中时仍把 DJ 模式的 tempo 指示同步出去。
    if (dj) {
      djMode.tempoGap = rtBeat.tempoGap;
      djMode.tempoConfidence = rtBeat.tempoConfidence;
    }
    return { hit: false, score: score, low: lowNorm, body: bodyNorm, vocal: vocalNorm, snap: snapNorm, tempoConfidence: rtBeat.tempoConfidence };
  }

  // 命中后根据本次间隔更新 tempoGap，并计算相对旧 tempo 的偏移。
  var gapShift = 0;
  if (rtBeat.lastHitAt > 0) {
    var gap = nowT - rtBeat.lastHitAt;
    while (gap > (dj ? 0.96 : 0.88)) gap *= 0.5;
    while (gap < (dj ? 0.32 : 0.42)) gap *= 2.0;
    if (gap >= (dj ? 0.32 : 0.42) && gap <= (dj ? 0.96 : 0.88)) {
      gapShift = rtBeat.tempoGap ? Math.abs(gap - rtBeat.tempoGap) / Math.max(0.001, rtBeat.tempoGap) : 0;
      var tempoEase = hasTempoLock ? (dj ? 0.12 : 0.10) : (dj ? 0.24 : 0.22);
      // DJ 模式下强低频可更快修正 tempo。
      if (dj && gapShift > 0.16 && strongTransient && lowDominance > 0.95) tempoEase = Math.min(0.36, tempoEase + gapShift * 0.45);
      rtBeat.tempoGap = rtBeat.tempoGap ? rtBeat.tempoGap * (1 - tempoEase) + gap * tempoEase : gap;
      rtBeat.tempoConfidence = Math.min(1, rtBeat.tempoConfidence + (tempoAssist ? (dj ? 0.04 : 0.04) : (dj ? 0.16 : 0.18)));
    }
  }
  rtBeat.lastHitAt = nowT;
  // 命中统计和分类统计。
  rtBeat.beatCount++;
  rtBeat.stats.hits++;
  if (tempoAssist) rtBeat.stats.assisted++;
  if (strongTransient || kickTransient) rtBeat.stats.strong++;
  // strength 是当前节拍用于视觉的强度，融合 score、低频存在感、低频主导度和 RMS 变化。
  var strength = dj
    ? clamp01(0.18 + score * 0.38 + lowPresence * 0.34 + Math.min(1.35, lowDominance) * 0.08 + rmsFlux * 0.72)
    : clamp01(0.24 + score * 0.36 + lowPresence * 0.34 + Math.min(1.25, lowDominance) * 0.07 + rmsFlux * 0.95);
  if (tempoAssist) strength = Math.max(strength, (dj ? 0.46 : 0.48) + rtBeat.tempoConfidence * (dj ? 0.10 : 0.10) + lowPresence * (dj ? 0.14 : 0.14));
  // 四拍循环标签用于给镜头动作分配 downbeat/push/drop/rebound 的差异。
  var comboSlot = (rtBeat.beatCount - 1) % 4;
  var combo = comboSlot === 0 ? 'downbeat' : (comboSlot === 1 ? 'push' : (comboSlot === 2 ? 'drop' : 'rebound'));
  if (strength > 0.84 && comboSlot !== 0) combo = 'accent';
  if (dj && strength > 0.78 && snapNorm > 0.56 && comboSlot !== 0) combo = 'accent';
  if (dj && gapShift > 0.14 && strongTransient && lowPresence > 0.52) combo = 'downbeat';
  rtBeat.pulse = Math.max(rtBeat.pulse, strength);
  if (dj) {
    // DJ 模式同步 tempo、段落变化和最后命中时间，供后续镜头动态使用。
    djMode.tempoGap = rtBeat.tempoGap;
    djMode.tempoConfidence = rtBeat.tempoConfidence;
    djMode.sectionChange = Math.max(djMode.sectionChange, Math.min(1, gapShift * 1.4));
    djMode.visualPulse = Math.max(djMode.visualPulse, strength);
    djMode.lastBeatAt = nowT;
  }
  return {
    // DJ 模式下稍微提前命中时间，抵消实时检测滞后。
    hit: true,
    time: dj ? Math.max(0, nowT - 0.026) : nowT,
    strength: strength,
    confidence: dj ? clamp01(score * 0.58 + lowPresence * 0.30 + rtBeat.tempoConfidence * 0.12) : clamp01(score * 0.62 + lowPresence * 0.26 + rtBeat.tempoConfidence * 0.12),
    low: Math.max(0.05, lowPresence),
    body: Math.max(0.02, bodyNorm * (dj ? 0.50 : 0.62)),
    snap: Math.max(0.02, snapNorm * (dj ? 0.86 : 1)),
    mass: dj ? clamp01(lowPresence * 0.84 + bodyNorm * 0.10) : clamp01(lowPresence * 0.76 + bodyNorm * 0.20),
    sharpness: dj ? clamp01(snapNorm * 0.58 + bodyNorm * 0.10) : clamp01(snapNorm * 0.70 + bodyNorm * 0.12),
    tempoAssist: tempoAssist,
    tempoGap: rtBeat.tempoGap,
    combo: combo,
    score: score,
    lowDominance: lowDominance,
    dj: dj
  };
}

// 把实时检测到的 beat 合并到已有 beatCam 事件，避免预解析和实时检测重复触发相机。
function mergeRealtimeBeatCamera(time, amp, tone) {
  // 在合并窗口内寻找距离最近的已有事件。
  var best = null;
  var bestDist = beatCam.realtimeMergeWindow;
  for (var i = 0; i < beatCam.events.length; i++) {
    var dist = Math.abs((beatCam.events[i].hit || 0) - time);
    if (dist < bestDist) {
      best = beatCam.events[i];
      bestDist = dist;
    }
  }
  if (!best) return false;
  // 合并后重设 hit/start，让相机事件与实时命中对齐。
  var nowT = audio ? audio.currentTime : uniforms.uTime.value;
  best.hit = time;
  best.start = nowT - (best.attack || beatCam.attack) * 0.42;
  var mergeMaxAmp = ((tone && tone.dj) || djMode.active) ? 0.62 : 0.62;
  best.amp = Math.min(mergeMaxAmp, Math.max(best.amp || 0, amp));
  if (tone) {
    // tone 中的各类幅度取最大值，保留更强的视觉表达。
    best.zoomAmp = Math.max(best.zoomAmp || 0, tone.zoomAmp);
    best.thetaAmp = Math.max(best.thetaAmp || 0, tone.thetaAmp);
    best.phiAmp = Math.max(best.phiAmp || 0, tone.phiAmp);
    best.rollAmp = Math.max(best.rollAmp || 0, tone.rollAmp || 0);
    best.low = Math.max(best.low || 0, tone.low);
    best.body = Math.max(best.body || 0, tone.body);
    best.snap = Math.max(best.snap || 0, tone.snap);
    best.mode = tone.mode || best.mode;
    best.dj = !!tone.dj || !!best.dj;
  }
  best.source = 'hybrid';
  beatCam.stats.merged++;
  return true;
}

// 把一个 beat 事件转换成相机冲击事件并加入 beatCam.events。
function scheduleBeatCamera(beat, source) {
  // 电影镜头关闭时不调度任何相机事件。
  if (!fx.cinema) return;
  // beat 可为数字时间或对象，下面统一拆出时间、强度和置信度。
  var time = typeof beat === 'number' ? beat : beat.time;
  if (!isFinite(time)) return;
  var strength = typeof beat === 'number' ? 0.72 : Math.max(0, Math.min(1, beat.strength || 0.72));
  var confidence = typeof beat === 'number' ? 0.72 : Math.max(0, Math.min(1, beat.confidence || 0.72));
  var isPrimary = typeof beat === 'number' ? true : beat.primary !== false;
  var visualImpact = typeof beat === 'number' ? strength : Math.max(0, Math.min(1, beat.impact == null ? strength : beat.impact));
  var isDjMapSource = source === 'djmap';
  var isMapSource = source === 'map' || !source;
  var isLiveSource = source === 'live' || source === 'fallback';
  var livePreview = !!(isLiveSource && beat && beat.preview);
  var dj = djMode.active && (isLiveSource || isDjMapSource || (beat && beat.dj));
  // 预解析 map 只接受 primary 或高强度事件，避免镜头过密。
  if (isMapSource && !isPrimary) return;
  if (isMapSource && visualImpact < 0.18 && strength < 0.56) return;
  if (isMapSource && confidence < 0.30 && strength < 0.68) return;
  var trackScale = cinemaTrackProfile.scale || 1;
  // 歌曲画像认为应柔和时，弱事件会被丢弃。
  if (trackScale < 0.58 && isMapSource && strength < 0.72 && visualImpact < 0.46) return;
  if (trackScale < 0.50 && isLiveSource && strength < (dj ? 0.58 : 0.84) && visualImpact < (dj ? 0.42 : 0.56)) return;
  var lowTone = typeof beat === 'number' ? 0.62 : Math.max(0, beat.low == null ? 0.62 : beat.low);
  var bodyTone = typeof beat === 'number' ? 0.22 : Math.max(0, beat.body == null ? 0.22 : beat.body);
  var snapTone = typeof beat === 'number' ? 0.16 : Math.max(0, beat.snap == null ? 0.16 : beat.snap);
  var rawLowTone = lowTone;
  var rawBodyTone = bodyTone;
  var rawSnapTone = snapTone;
  var toneSum = Math.max(0.001, lowTone + bodyTone + snapTone);
  // 低频、身体感和清脆感归一化后用于决定镜头模式。
  lowTone /= toneSum;
  bodyTone /= toneSum;
  snapTone /= toneSum;
  var sharpness = typeof beat === 'number' ? snapTone : Math.max(0, Math.min(1, beat.sharpness == null ? snapTone : beat.sharpness));
  var mass = typeof beat === 'number' ? lowTone : Math.max(0, Math.min(1, beat.mass == null ? (lowTone * 0.72 + bodyTone * 0.36 + strength * 0.20) : beat.mass));
  var nowT = audio ? audio.currentTime : uniforms.uTime.value;
  // mode 决定镜头动作类型：deep 偏推拉，body 偏俯仰，snap 偏滚转。
  var mode = 'deep';
  if (dj) {
    if (rawSnapTone > 0.58 && rawSnapTone > rawLowTone * 0.86 && rawSnapTone > rawBodyTone * 1.08) mode = 'snap';
    else if (rawBodyTone > 0.36 && rawBodyTone > rawLowTone * 0.56) mode = 'body';
  } else {
    if (snapTone > 0.42 && snapTone > lowTone * 1.18 && snapTone > bodyTone * 1.08) mode = 'snap';
    else if (bodyTone > 0.46 && bodyTone > lowTone * 1.12) mode = 'body';
  }
  var amp;
  if (dj) {
    // DJ 模式按原始 tone 重新计算 drive，保持低频主导。
    var lowDrive = clamp01((rawLowTone - 0.42) / 0.54);
    var bodyDrive = clamp01((rawBodyTone - 0.24) / 0.58);
    var snapDrive = clamp01((rawSnapTone - 0.30) / 0.60);
    if (mode === 'deep') amp = 0.16 + strength * 0.20 + lowDrive * 0.25 + confidence * 0.05;
    else if (mode === 'body') amp = 0.12 + strength * 0.15 + bodyDrive * 0.18 + lowDrive * 0.06;
    else amp = 0.08 + strength * 0.11 + snapDrive * 0.13;
  } else {
    amp = Math.max(0.18, Math.min(0.72, 0.15 + strength * 0.34 + confidence * 0.06 + mass * 0.13 + snapTone * 0.04));
  }
  if (isMapSource) amp *= 0.68 + visualImpact * 0.46;
  if (!isPrimary) amp *= 0.62;
  if (source === 'fallback') amp *= 0.74;
  if (source === 'live') amp *= dj ? 0.62 : (livePreview ? 0.78 : 0.92);
  if (mode === 'deep' && !dj) amp = Math.min(0.62, amp * 1.12);
  // 歌曲画像动态缩放会整体影响本次相机冲击。
  var dynScale = cameraDynamicsScale(0.92 + visualImpact * 0.12 + mass * 0.08);
  amp *= dj ? clampRange(dynScale, 0.72, 1.16) : dynScale;
  var attack = dj
    ? (mode === 'snap' ? 0.010 : (mode === 'body' ? 0.015 : 0.017))
    : Math.max(0.014, Math.min(0.038, beatCam.attack * (1.18 - sharpness * 0.55)));
  var hold = dj
    ? (mode === 'deep' ? 0.038 + lowTone * 0.014 : (mode === 'body' ? 0.026 : 0.014))
    : Math.max(0.014, Math.min(0.052, beatCam.hold * (0.62 + lowTone * 0.55 + bodyTone * 0.25)));
  var release = dj
    ? (mode === 'deep' ? 0.178 + mass * 0.040 : (mode === 'body' ? 0.140 : 0.104))
    : Math.max(0.110, Math.min(0.255, beatCam.release * (0.76 + mass * 0.56 + bodyTone * 0.18 - sharpness * 0.18)));
  var idx = typeof beat === 'number' ? Math.floor(time * 2.7) : (beat.index || Math.floor(time * 2.7));
  var combo = typeof beat === 'number' ? null : beat.combo;
  if (!combo) {
    // 没有外部 combo 时按事件索引生成四拍循环动作标签。
    var comboSlot = Math.abs(idx) % 4;
    combo = comboSlot === 0 ? 'downbeat' : (comboSlot === 1 ? 'push' : (comboSlot === 2 ? 'drop' : 'rebound'));
  }
  // 基础镜头幅度拆成推拉、水平、垂直和滚转四类。
  var zoomAmp = 0.070 + mass * 0.190 + (mode === 'deep' ? 0.095 : 0.018) + strength * 0.045;
  var thetaAmp = 0.00035;
  var phiAmp = 0.002 + (mode === 'body' ? 0.012 : (mode === 'snap' ? 0.005 : 0.002));
  var rollAmp = mode === 'snap' ? (0.003 + snapTone * 0.004) : 0.0008;
  zoomAmp *= 0.76 + dynScale * 0.28;
  phiAmp *= 0.82 + dynScale * 0.20;
  rollAmp *= 0.78 + dynScale * 0.24;
  if (dj) {
    // DJ 模式重算各镜头通道，使 deep/body/snap 的差异更明确。
    var lowDrive2 = clamp01((rawLowTone - 0.42) / 0.54);
    var bodyDrive2 = clamp01((rawBodyTone - 0.24) / 0.58);
    var snapDrive2 = clamp01((rawSnapTone - 0.30) / 0.60);
    if (mode === 'deep') {
      zoomAmp = 0.115 + lowDrive2 * 0.170 + strength * 0.036;
      phiAmp = 0.0016 + bodyDrive2 * 0.0022;
      thetaAmp = 0.0006 + bodyDrive2 * 0.0012;
      rollAmp = 0.0006 + snapDrive2 * 0.0016;
    } else if (mode === 'body') {
      zoomAmp = 0.052 + lowDrive2 * 0.052;
      phiAmp = 0.0075 + bodyDrive2 * 0.018;
      thetaAmp = 0.0018 + bodyDrive2 * 0.0046;
      rollAmp = 0.0014 + snapDrive2 * 0.0022;
    } else {
      zoomAmp = 0.026 + lowDrive2 * 0.024;
      phiAmp = 0.0024 + bodyDrive2 * 0.0040;
      thetaAmp = 0.0009 + snapDrive2 * 0.0018;
      rollAmp = 0.0048 + snapDrive2 * 0.0095;
    }
    if (combo === 'downbeat') {
      // downbeat 重点强化推拉。
      amp *= 1.12;
      zoomAmp *= mode === 'deep' ? 1.28 : 1.06;
      phiAmp *= 0.76;
    } else if (combo === 'push') {
      // push 弱化推拉，增强左右偏移。
      amp *= mode === 'deep' ? 0.76 : 0.68;
      zoomAmp *= 0.62;
      thetaAmp *= 1.15;
    } else if (combo === 'drop') {
      // drop 偏向垂直冲击。
      amp *= 0.82;
      zoomAmp *= 0.50;
      phiAmp *= 1.38;
    } else if (combo === 'rebound') {
      // rebound 作为弱回弹。
      amp *= 0.62;
      zoomAmp *= 0.40;
      phiAmp *= 0.70;
    } else if (combo === 'accent') {
      // accent 更强调滚转或局部装饰。
      amp *= mode === 'snap' ? 0.78 : 0.94;
      zoomAmp *= mode === 'snap' ? 0.42 : 0.78;
      rollAmp *= 1.58;
    }
    if (isDjMapSource) {
      // 离线 DJ beatMap 事件根据 visualImpact 重新拉开强弱对比。
      var offlineContrast = Math.pow(clamp01((visualImpact - 0.16) / 0.72), 1.06);
      var offlineDrive = 0.72 + offlineContrast * 0.94 + Math.pow(strength, 1.22) * 0.14;
      var sectionLowGate = clamp01(((djMode.sectionLow || 0) - 0.030) / 0.32);
      var sectionEnergyGate = clamp01(((djMode.sectionEnergy || 0) - 0.045) / 0.40);
      var liveSectionGate = Math.max(sectionLowGate * 0.58 + sectionEnergyGate * 0.34, visualImpact * 0.82);
      var weakSectionScale = 0.54 + Math.pow(clamp01(liveSectionGate), 0.78) * 0.46;
      var comboDrive = combo === 'downbeat'
        ? 0.96 + offlineContrast * 0.38
        : (combo === 'drop'
          ? 0.80 + offlineContrast * 0.26
          : (combo === 'accent'
            ? 0.74 + offlineContrast * 0.30
          : (combo === 'push' ? 0.68 + offlineContrast * 0.16 : 0.52 + offlineContrast * 0.12)));
      if (mode === 'deep') {
        // deep 离线事件主要放大推拉和持续时间。
        amp *= offlineDrive * comboDrive * 1.38;
        zoomAmp *= 1.14 + offlineContrast * 0.68 + lowDrive2 * 0.20;
        phiAmp *= 0.72 + offlineContrast * 0.22;
        thetaAmp *= 0.72 + offlineContrast * 0.20;
        release *= 0.98 + offlineContrast * 0.20;
      } else if (mode === 'body') {
        // body 离线事件增强俯仰和横向微动。
        amp *= offlineDrive * comboDrive * 1.24;
        zoomAmp *= 0.90 + offlineContrast * 0.32;
        phiAmp *= 1.00 + offlineContrast * 0.42 + bodyDrive2 * 0.18;
        thetaAmp *= 0.98 + offlineContrast * 0.36 + bodyDrive2 * 0.14;
        release *= 0.96 + offlineContrast * 0.12;
      } else {
        // snap 离线事件压低推拉，增强滚转和短促感。
        amp *= offlineDrive * comboDrive * 0.94;
        zoomAmp *= 0.52 + offlineContrast * 0.24;
        phiAmp *= 0.84 + offlineContrast * 0.28;
        thetaAmp *= 0.86 + offlineContrast * 0.30;
        rollAmp *= 1.02 + offlineContrast * 0.76 + snapDrive2 * 0.22;
        attack *= 0.92;
        release *= 0.78 + offlineContrast * 0.14;
      }
      if (combo === 'downbeat') {
        // downbeat 离线事件再按对比度加强推拉。
        zoomAmp *= mode === 'deep' ? (1.04 + offlineContrast * 0.18) : (0.96 + offlineContrast * 0.12);
      } else if (combo === 'drop') {
        phiAmp *= 0.96 + offlineContrast * 0.28;
      } else if (combo === 'accent') {
        rollAmp *= 1.02 + offlineContrast * 0.34;
        zoomAmp *= 0.72 + offlineContrast * 0.20;
      }
      var peakTame = Math.pow(clamp01((visualImpact - 0.76) / 0.24), 1.35);
      if (peakTame > 0) {
        // 顶部强度做轻微驯化，避免高 impact beatMap 让相机过冲。
        var downbeatTame = combo === 'downbeat' ? 1.0 : 0.58;
        amp *= 1 - peakTame * (0.070 + downbeatTame * 0.050);
        zoomAmp *= 1 - peakTame * (0.060 + downbeatTame * 0.050);
        phiAmp *= 1 - peakTame * 0.035;
        release *= 1 - peakTame * 0.045;
      }
      if (visualImpact < 0.12 && liveSectionGate < 0.18) {
        // 离线弱事件且实时段落也很弱时整体收缩，避免安静段仍有大镜头。
        var softScale = Math.min(1, weakSectionScale * (0.72 + visualImpact * 1.10));
        amp *= softScale;
        zoomAmp *= 0.58 + softScale * 0.34;
        phiAmp *= 0.62 + softScale * 0.30;
        thetaAmp *= 0.62 + softScale * 0.28;
        rollAmp *= 0.66 + softScale * 0.24;
        release *= 0.86 + softScale * 0.16;
      }
    }
  } else if (combo === 'downbeat') {
    // 普通模式下按 combo 对镜头通道做基础差异化。
    amp *= 1.10;
    zoomAmp *= 1.18;
    phiAmp *= 0.72;
  } else if (combo === 'push') {
    amp *= 0.84;
    zoomAmp *= 0.88;
    phiAmp *= 0.62;
  } else if (combo === 'drop') {
    amp *= 0.96;
    zoomAmp *= 0.72;
    phiAmp *= 1.22;
  } else if (combo === 'rebound') {
    amp *= 0.74;
    zoomAmp *= 0.62;
    phiAmp *= 0.78;
  } else if (combo === 'accent') {
    amp *= 1.14;
    zoomAmp *= 1.08;
    rollAmp *= 1.35;
  }
  if (livePreview && !dj) {
    // beatMap 未就绪时的实时预览镜头更克制。
    var previewTone = clamp01(visualImpact * 0.54 + rawLowTone * 0.22 + confidence * 0.18 + strength * 0.06);
    amp *= 0.72 + previewTone * 0.16;
    zoomAmp *= 0.62 + previewTone * 0.18;
    phiAmp *= 0.70 + previewTone * 0.12;
    thetaAmp *= 0.70 + previewTone * 0.12;
    rollAmp *= 0.54 + previewTone * 0.16;
    release *= 1.08 + previewTone * 0.08;
  }
  // DJ 离线事件设置软上限，保留强弱但避免连续强事件太晃。
  if (dj && isDjMapSource && amp > 0.74) amp = 0.74 + (amp - 0.74) * 0.56;
  if (dj && isDjMapSource && zoomAmp > 0.30) zoomAmp = 0.30 + (zoomAmp - 0.30) * 0.52;
  amp = Math.max(dj ? (isDjMapSource ? 0.018 : 0.040) : 0.08, Math.min(dj ? (isDjMapSource ? 0.92 : 0.34) : 0.68, amp));
  if (isLiveSource) {
    // 实时来源额外限频，防止同一鼓点附近重复触发。
    var liveMinInterval = dj ? Math.max(0.315, Math.min(0.500, rtBeat.tempoGap ? rtBeat.tempoGap * 0.62 : 0.360)) : beatCam.realtimeMinInterval;
    if (time - beatCam.lastRealtimeAt < liveMinInterval && strength < (dj ? 0.74 : 0.78)) {
      beatCam.stats.liveBlocked++;
      return;
    }
    beatCam.lastRealtimeAt = time;
    // 优先尝试和已有预解析事件合并。
    if (mergeRealtimeBeatCamera(time, amp, {
      zoomAmp: zoomAmp, thetaAmp: thetaAmp, phiAmp: phiAmp, rollAmp: rollAmp, mode: mode,
      low: lowTone, body: bodyTone, snap: snapTone, dj: dj
    })) {
      beatCam.lastTriggerAt = Math.max(beatCam.lastTriggerAt, time);
      return;
    }
    for (var ei = beatCam.events.length - 1; ei >= 0; ei--) {
      // 如果实时命中抢在很近的 map 事件前，删除那个 map 事件，避免双触发。
      var pending = beatCam.events[ei];
      if (pending.source === 'map' && pending.hit > time && pending.hit - time < beatCam.realtimeMergeWindow) {
        beatCam.events.splice(ei, 1);
      }
    }
  }
  if (isDjMapSource) {
    // 离线 DJ map 事件按 step 控制最小间隔。
    var djGap = time - beatCam.lastTriggerAt;
    var djMinGap = Math.max(0.255, Math.min(0.470, (beat && beat.step ? beat.step * 0.52 : 0.320)));
    if (djGap < djMinGap && strength < 0.86) return;
    beatCam.lastTriggerAt = time;
    beatCam.stats.map++;
  } else if (!isLiveSource) {
    // 普通 map 事件使用 beatCam.minInterval，primary 事件可以略微放宽。
    var gap = time - beatCam.lastTriggerAt;
    var minGap = beatCam.minInterval;
    if (isMapSource && isPrimary) minGap *= 0.82;
    if (gap < minGap && strength < 0.88) return;
    beatCam.lastTriggerAt = time;
    beatCam.stats.map++;
  } else {
    // 实时事件只推进 lastTriggerAt 和 live 统计。
    beatCam.lastTriggerAt = Math.max(beatCam.lastTriggerAt, time);
    beatCam.stats.live++;
  }
  // 写入最终相机事件，updateBeatCamera 会按 attack/hold/release 消费它。
  beatCam.events.push({
    start: isLiveSource ? nowT - attack * 0.42 : nowT + (time - nowT) - attack,
    hit: time,
    amp: amp,
    attack: attack,
    hold: hold,
    release: release,
    zoomAmp: zoomAmp,
    thetaAmp: thetaAmp,
    phiAmp: phiAmp,
    rollAmp: rollAmp,
    mode: mode,
    combo: combo,
    phase: idx * 2.399963 + (snapTone - lowTone) * 1.4,
    low: lowTone,
    body: bodyTone,
    snap: snapTone,
    mass: mass,
    source: source || 'map',
    dj: dj
  });
  // 保留有限数量的未来/活动事件，避免长时间播放后事件数组增长。
  var maxEvents = djMode.active ? 12 : 8;
  if (beatCam.events.length > maxEvents) beatCam.events.splice(0, beatCam.events.length - maxEvents);
}

// 每帧消费 beatCam.events，生成当前帧的相机冲击偏移。
function updateBeatCamera(dt) {
  var t = audio ? audio.currentTime : uniforms.uTime.value;
  if (!audio || audio.paused) {
    // 暂停时快速衰减所有镜头冲击并清空待触发事件。
    beatCam.punch *= Math.pow(0.08, dt);
    beatCam.thetaKick *= Math.pow(0.05, dt);
    beatCam.phiKick *= Math.pow(0.05, dt);
    beatCam.radiusKick *= Math.pow(0.05, dt);
    beatCam.rollKick *= Math.pow(0.05, dt);
    beatCam.events.length = 0;
    beatCam.prevAudioTime = t;
    return;
  }
  if (beatCam.prevAudioTime >= 0 && Math.abs(t - beatCam.prevAudioTime) > 0.55) {
    // 检测到 seek 或播放时间跳变后重新对齐 beatMap 游标。
    if (djMode.active) syncDjBeatMapCursor(t, false);
    else syncBeatCameraToTime(t);
  }
  beatCam.prevAudioTime = t;

  // 本帧镜头冲击的各通道累计值。
  var punch = 0;
  var thetaKick = 0;
  var phiKick = 0;
  var radiusKick = 0;
  var rollKick = 0;
  var leadEvent = null;
  var leadPunch = 0;
  var leadVal = 0;
  for (var i = beatCam.events.length - 1; i >= 0; i--) {
    // 每个事件按 attack/hold/release 计算局部强度。
    var ev = beatCam.events[i];
    var attack = ev.attack || beatCam.attack;
    var hold = ev.hold || beatCam.hold;
    var release = ev.release || beatCam.release;
    var local = t - ev.start;
    var val = 0;
    if (local < 0) {
      val = 0;
    } else if (local < attack) {
      val = easeBeatCamera(local / attack);
    } else if (local < attack + hold) {
      val = 1;
    } else if (local < attack + hold + release) {
      var r = (local - attack - hold) / release;
      val = 1 - easeBeatCamera(r);
    } else {
      // 事件生命周期结束后移出队列。
      beatCam.events.splice(i, 1);
      continue;
    }
    var evPunch = val * ev.amp;
    punch = Math.max(punch, evPunch);
    if (evPunch > leadPunch) {
      // leadEvent 是本帧最强事件，后续按它决定方向和 combo 动作。
      leadEvent = ev;
      leadPunch = evPunch;
      leadVal = val;
    }
  }
  if (leadEvent) {
    // phase 决定左右方向，snapFlick 让 snap 类动作前段更锋利。
    var sign = Math.sin(leadEvent.phase) >= 0 ? 1 : -1;
    var snapFlick = 1.0 - Math.min(1, Math.max(0, leadVal - 0.25) / 0.75);
    var combo = leadEvent.combo || 'downbeat';
    if (combo === 'downbeat') {
      // downbeat 主要推拉相机。
      radiusKick = leadPunch * leadEvent.zoomAmp;
      phiKick = -leadPunch * 0.0032;
    } else if (combo === 'push') {
      // push 是较弱推拉。
      radiusKick = leadPunch * leadEvent.zoomAmp * 0.72;
      phiKick = -leadPunch * 0.0014;
    } else if (combo === 'drop') {
      // drop 更偏垂直俯仰。
      radiusKick = leadPunch * leadEvent.zoomAmp * 0.46;
      phiKick = leadPunch * leadEvent.phiAmp * 0.92;
    } else if (combo === 'rebound') {
      // rebound 是轻微回弹。
      radiusKick = leadPunch * leadEvent.zoomAmp * 0.30;
      phiKick = -leadPunch * leadEvent.phiAmp * 0.22;
    } else if (combo === 'accent') {
      // accent 叠加滚转，适合清脆高频。
      radiusKick = leadPunch * leadEvent.zoomAmp * 0.90;
      phiKick = -leadPunch * 0.0022;
      rollKick = sign * leadPunch * (leadEvent.rollAmp || 0) * (0.45 + snapFlick * 0.30);
    } else if (leadEvent.mode === 'deep') {
      // 没有 combo 但 mode 为 deep 时走默认低频推拉。
      radiusKick = leadPunch * leadEvent.zoomAmp;
      phiKick = -leadPunch * 0.003;
    }
    if (leadEvent.dj) {
      // DJ 事件额外增加左右微动和 snap 滚转。
      var djSide = sign * leadPunch * (leadEvent.thetaAmp || 0.0012) * (0.70 + (leadEvent.body || 0) * 0.65 + (leadEvent.snap || 0) * 0.35);
      thetaKick += djSide;
      if (leadEvent.mode === 'snap' || combo === 'accent') {
        rollKick += sign * leadPunch * (leadEvent.rollAmp || 0.003) * (0.52 + snapFlick * 0.34);
      }
      if (combo === 'downbeat') radiusKick *= 1.06;
      else if (combo === 'drop') phiKick *= 1.18;
      punch = Math.min(0.90, punch * (1.04 + (leadEvent.mass || 0) * 0.10));
    }
  }
  // 将目标冲击平滑写入 beatCam，攻击快、释放慢，避免相机抖成硬切。
  var djEase = djMode.active;
  beatCam.punch += (punch - beatCam.punch) * (punch > beatCam.punch ? (djEase ? 0.82 : 0.72) : (djEase ? 0.44 : 0.38));
  beatCam.thetaKick += (thetaKick - beatCam.thetaKick) * (Math.abs(thetaKick) > Math.abs(beatCam.thetaKick) ? (djEase ? 0.80 : 0.70) : (djEase ? 0.42 : 0.36));
  beatCam.phiKick += (phiKick - beatCam.phiKick) * (Math.abs(phiKick) > Math.abs(beatCam.phiKick) ? (djEase ? 0.80 : 0.70) : (djEase ? 0.42 : 0.36));
  beatCam.radiusKick += (radiusKick - beatCam.radiusKick) * (radiusKick > beatCam.radiusKick ? (djEase ? 0.82 : 0.72) : (djEase ? 0.40 : 0.34));
  beatCam.rollKick += (rollKick - beatCam.rollKick) * (Math.abs(rollKick) > Math.abs(beatCam.rollKick) ? (djEase ? 0.82 : 0.72) : (djEase ? 0.44 : 0.38));
}

// 解除中心锁定，让用户轨道相机重新接管中心以外的偏移。
function unlockCenteredView() {
  orbit.centerLocked = false;
}

// 清理所有会让视图偏离中心的输入偏移。
function clearCenteredViewOffsets() {
  // 指针视差目标和当前值都归零。
  pointerTarget.x = 0;
  pointerTarget.y = 0;
  pointerParallax.x = 0;
  pointerParallax.y = 0;
  mouseWorld.set(-999, -999, 0);
  mouseActive = false;
  headParallax.x = 0;
  headParallax.y = 0;
  headParallax.active = false;
  headNeutral = null;
  if (typeof particleRotation !== 'undefined') {
    // 粒子拖拽旋转归零。
    particleRotation.x = 0;
    particleRotation.y = 0;
  }
  if (typeof particleSpin !== 'undefined') {
    // 粒子惯性速度归零。
    particleSpin.vx = 0;
    particleSpin.vy = 0;
  }
  if (typeof particlePointerSpin !== 'undefined') particlePointerSpin.active = false;
  if (typeof resetParticleRotationTarget === 'function') resetParticleRotationTarget(false);
}

// 根据轨道相机、焦点跟拍、电影镜头和自由相机状态更新主相机。
function updateCamera() {
  // 自由相机优先级最高，启用时直接返回。
  if (applyFreeCameraToCamera()) return;
  if (orbit.recentering) {
    // 回正时用户轨道参数缓慢靠近基准值。
    orbit.userTheta  += (orbit.baselineTheta - orbit.userTheta)  * 0.04;
    orbit.userPhi    += (orbit.baselinePhi   - orbit.userPhi)    * 0.04;
    orbit.userRadius += (orbit.baselineRadius- orbit.userRadius) * 0.04;
    if (Math.abs(orbit.userTheta - orbit.baselineTheta) < 0.005 &&
        Math.abs(orbit.userPhi - orbit.baselinePhi) < 0.005 &&
        Math.abs(orbit.userRadius - orbit.baselineRadius) < 0.05) {
      orbit.userTheta = orbit.baselineTheta;
      orbit.userPhi   = orbit.baselinePhi;
      orbit.userRadius= orbit.baselineRadius;
      orbit.recentering = false;
    }
  }

  // v8: focus 优先, 否则用 user + cine 复合姿态
  var fa = orbit.focus.active;
  // target* 是本帧相机要缓动靠近的目标轨道参数。
  var targetTheta, targetPhi, targetRadius, tLookAt;
  if (fa) {
    // 焦点跟拍优先，例如悬停歌单架或队列面板。
    targetTheta = orbit.focus.theta;
    targetPhi   = orbit.focus.phi;
    targetRadius = orbit.focus.radius;
    tLookAt = orbit.focus.lookAt;
  } else if (orbit.centerLocked) {
    // 中心锁定时忽略用户拖拽，只叠加电影镜头偏移。
    targetTheta = orbit.baselineTheta + orbit.cineTheta;
    targetPhi = Math.max(orbit.minPhi, Math.min(orbit.maxPhi, orbit.baselinePhi + orbit.cinePhi));
    targetRadius = Math.max(orbit.minRadius, Math.min(orbit.maxRadius, orbit.baselineRadius + orbit.cineRadius));
    tLookAt = ZERO_VEC;
  } else {
    // 普通轨道模式：用户轨道和电影镜头偏移叠加。
    targetTheta = orbit.userTheta + orbit.cineTheta;
    targetPhi   = Math.max(orbit.minPhi, Math.min(orbit.maxPhi, orbit.userPhi + orbit.cinePhi));
    targetRadius= Math.max(orbit.minRadius, Math.min(orbit.maxRadius, orbit.userRadius + orbit.cineRadius));
    tLookAt = ZERO_VEC;
  }
  // 丝滑变速: 线性 lerp 自然给出 "快→慢" 缓出曲线
  var focusEase = fa ? 0.16 : 0.10;
  var radiusEase = fa ? 0.12 : 0.07;
  if (beatCam.punch > 0.01) {
    // 节拍冲击强时略微提高相机跟随速度，避免动作滞后。
    focusEase = Math.max(focusEase, 0.12 + beatCam.punch * 0.12);
    radiusEase = Math.max(radiusEase, 0.09 + beatCam.punch * 0.12);
  }
  orbit.theta  += (targetTheta  - orbit.theta)  * focusEase;
  orbit.phi    += (targetPhi    - orbit.phi)    * focusEase;
  orbit.radius += (targetRadius - orbit.radius) * radiusEase;
  orbit.lookAt.x += (tLookAt.x - orbit.lookAt.x) * focusEase;
  orbit.lookAt.y += (tLookAt.y - orbit.lookAt.y) * focusEase;
  orbit.lookAt.z += (tLookAt.z - orbit.lookAt.z) * focusEase;

  // 球坐标转笛卡尔坐标，得到相机在 lookAt 周围的位置。
  var cy = Math.cos(orbit.phi), sy = Math.sin(orbit.phi);
  var ct = Math.cos(orbit.theta), st = Math.sin(orbit.theta);
  camera.position.set(
    orbit.lookAt.x + orbit.radius * cy * st,
    orbit.lookAt.y + orbit.radius * sy,
    orbit.lookAt.z + orbit.radius * cy * ct
  );
  // 相机始终看向当前平滑后的 lookAt 点。
  camera.lookAt(orbit.lookAt);
  var cameraShake = clampRange(Number(fx.cinemaShake) || 0, 0, 1.8);
  // beatCam.rollKick 最后叠加到相机 roll。
  camera.rotation.z += beatCam.rollKick * cameraShake;

  // 节拍 punch 会短暂改变 FOV，形成镜头冲击。
  var cameraPunch = Math.max(camPunch * 0.55, beatCam.punch * 0.54 + beatCam.radiusKick * 0.16) * cameraShake;
  var targetFOV = BASE_FOV - cameraPunch * (djMode.active ? 2.62 : 2.35);
  var fovEase = targetFOV < camera.fov ? 0.24 : 0.12;
  camera.fov += (targetFOV - camera.fov) * fovEase;
  camera.updateProjectionMatrix();
  camPunch *= 0.86;
}

// 焦点跟拍 (hover 0.5s 后镜头移到目标)
// 记录当前希望进入的焦点区以及进入/退出延迟计时器。
var focusHover = { wantType: null, pendingTimer: null, exitTimer: null };
// 星河/壁纸预设下使用更保守的歌单架相机构图。
function shouldUseWallpaperSafeShelfCamera() {
  return !!(fx && Number(fx.preset) === 5);
}
// 骷髅预设下使用专门的歌单架安全构图。
function shouldUseSkullSafeShelfCamera() {
  return !!(fx && Number(fx.preset) === SKULL_PRESET_INDEX);
}
// 星河预设且歌词相机锁开启时，歌词相机需要额外锁定。
function shouldUseWallpaperLyricCameraLock() {
  return !!(fx && Number(fx.preset) === 5 && fx.lyricCameraLock);
}
// 请求舞台歌词相机在后续若干帧强制贴合主相机。
function requestStageLyricCameraSnap(frames) {
  if (typeof stageLyrics === 'undefined' || !stageLyrics) return;
  stageLyrics.snapCameraLockFrames = Math.max(stageLyrics.snapCameraLockFrames || 0, frames || 8);
}
// 星河预设下，歌单架打开时是否压暗壁纸层。
function shouldDimWallpaperForShelf() {
  if (!shouldUseWallpaperSafeShelfCamera()) return false;
  if (!shelfManager || !shelfManager.getMode || shelfManager.getMode() !== 'side') return false;
  if (shelfPinnedOpen) return true;
  return !!(shelfManager.hasOpenContent && shelfManager.hasOpenContent());
}
// 侧边歌单详情打开时，歌词需要避让右侧内容。
function shouldOffsetLyricsForShelfDetail() {
  if (!shelfManager || !shelfManager.getMode || shelfManager.getMode() !== 'side') return false;
  return !!(shelfManager.hasOpenContent && shelfManager.hasOpenContent());
}
// 判断当前是否应让舞台歌词避开歌单架区域。
function shouldAvoidStageLyricsForShelf() {
  if (!shelfManager || !shelfManager.getMode || shelfManager.getMode() !== 'side') return false;
  if (shelfAlwaysVisible()) return true;
  if (shelfPinnedOpen) return true;
  if (shelfManager.hasOpenContent && shelfManager.hasOpenContent()) return true;
  return !!(shelfVisibility > 0.24 || (shelfHoverCue && shelfHoverCue.value > 0.28));
}
// 激活指定焦点区，并写入 orbit.focus 的目标轨道参数。
function activateFocusZone(type) {
  // 焦点区接管前解除中心锁，允许相机移动到侧边或队列目标。
  unlockCenteredView();
  orbit.focus.active = true;
  orbit.focus.type = type;
  var shelfProfile = shelfLayoutProfile();
  if (type === 'shelf-side') {
    // 右侧歌单架焦点。
    if (shouldUseWallpaperSafeShelfCamera()) {
      orbit.focus.theta  = shelfProfile.portrait ? 0.18 : 0.24;
      orbit.focus.phi    = shelfProfile.portrait ? 0.00 : 0.02;
      orbit.focus.radius = shelfProfile.portrait ? 5.74 : 5.32;
      orbit.focus.lookAt.set(shelfProfile.portrait ? 1.04 : 2.24, -0.08, 0.78);
      camPunch = Math.max(camPunch, 0.28);
      requestStageLyricCameraSnap(10);
    } else {
      // 侧栏 (右): 近一点、侧一点，让歌单架打开时有明确的镜头推近。
      orbit.focus.theta  = shelfProfile.portrait ? 0.24 : 0.42;
      orbit.focus.phi    = shelfProfile.portrait ? -0.06 : -0.12;
      orbit.focus.radius = shelfProfile.portrait ? 5.28 : 4.20;
      orbit.focus.lookAt.set(shelfProfile.portrait ? 1.08 : 2.32, shelfProfile.portrait ? -0.18 : -0.10, 0.72);
      camPunch = Math.max(camPunch, 0.82);
    }
  } else if (type === 'shelf-detail') {
    // 歌单架二级详情焦点。
    if (shouldUseWallpaperSafeShelfCamera()) {
      orbit.focus.theta  = shelfProfile.portrait ? 0.16 : 0.26;
      orbit.focus.phi    = shelfProfile.portrait ? -0.02 : 0.02;
      orbit.focus.radius = shelfProfile.portrait ? 5.88 : 5.18;
      orbit.focus.lookAt.set(shelfProfile.portrait ? 0.72 : 2.28, shelfProfile.portrait ? -0.36 : -0.32, 0.84);
      camPunch = Math.max(camPunch, 0.30);
      requestStageLyricCameraSnap(10);
    } else {
      orbit.focus.theta  = shelfProfile.portrait ? 0.16 : 0.34;
      orbit.focus.phi    = shelfProfile.portrait ? -0.03 : -0.06;
      orbit.focus.radius = shelfProfile.portrait ? 5.90 : 4.86;
      orbit.focus.lookAt.set(shelfProfile.portrait ? 0.62 : 1.74, shelfProfile.portrait ? -0.08 : 0.02, 0.82);
      camPunch = Math.max(camPunch, 0.38);
    }
  } else if (type === 'shelf-stage') {
    // 舞台: 居中仰拍
    orbit.focus.theta  = 0.0;
    orbit.focus.phi    = shelfProfile.portrait ? -0.24 : -0.32;
    orbit.focus.radius = shelfProfile.portrait ? 4.8 : 3.8;
    orbit.focus.lookAt.set(0, shelfProfile.portrait ? -1.86 : -1.7, 0.8);
  } else if (type === 'queue') {
    // 队列在左侧 HTML 面板, 相机微微左移 + 抬升
    orbit.focus.theta  = 0.40;
    orbit.focus.phi    = 0.05;
    orbit.focus.radius = 5.8;
    orbit.focus.lookAt.set(-1.2, 0, 0);
  }
}
// 请求进入或退出某个焦点区，带延迟避免鼠标路过时频繁切镜头。
function setFocusZone(type, immediate) {
  if (type && !shouldUseShelfDynamicCamera(type)) {
    // 配置不允许歌单架动态相机时，shelf 类焦点请求会被清空。
    if (/^shelf-/.test(String(orbit.focus.type || ''))) orbit.focus.active = false;
    type = null;
  }
  if (focusHover.wantType === type) return;
  focusHover.wantType = type;
  if (focusHover.pendingTimer) { clearTimeout(focusHover.pendingTimer); focusHover.pendingTimer = null; }
  if (focusHover.exitTimer) { clearTimeout(focusHover.exitTimer); focusHover.exitTimer = null; }
  if (!type) {
    // 立刻退出 focus, 让相机回主姿态 (但插值是平滑的)
    var exitDelay = orbit.focus.type === 'queue' ? PEEK_HIDE_DELAY : 120;
    focusHover.exitTimer = setTimeout(function(){
      focusHover.exitTimer = null;
      if (!focusHover.wantType) orbit.focus.active = false;
    }, exitDelay);
    return;
  }
  if (immediate) {
    // immediate 用于点击打开等明确操作，跳过悬停延迟。
    activateFocusZone(type);
    return;
  }
  // 延迟 500ms 激活
  focusHover.pendingTimer = setTimeout(function(){
    focusHover.pendingTimer = null;
    if (focusHover.wantType !== type) return;
    activateFocusZone(type);
  }, 260);
}

// 电影镜头 v8: 振幅大幅减小, 节拍 punch 加冷却 + 强度门槛
//   - cineTheta/Phi 是非常缓慢的低频漂移, 不再让人 motion sick
//   - punch zoom 只在 真·强主拍 触发, 至少间隔 0.45s, 振幅 ×0.5
// 上一次普通镜头 punch 的时间，用于冷却。
var lastCamPunchAt = -10;
// 普通镜头 punch 最小间隔。
var CAM_PUNCH_MIN_INTERVAL = 0.45;     // 秒
// 普通镜头 punch 强度阈值。
var CAM_PUNCH_BEAT_THRESHOLD = 0.55;   // 必须够强才触发
// 更新电影镜头的低频漂移和节拍偏移。
function updateCinema(dt) {
  // cinemaT 是慢速漂移的时间基准。
  cinemaT += dt;
  // 先更新节拍相机通道，cine 偏移会叠加这些结果。
  updateBeatCamera(dt);
  if (!fx.cinema) {
    // 关闭电影镜头时逐帧衰减残留偏移。
    orbit.cineTheta  *= 0.95;
    orbit.cinePhi    *= 0.95;
    orbit.cineRadius *= 0.95;
    return;
  }
  var damp = orbit.rotating ? 0.25 : 1.0;
  // v8: 振幅减半, 周期更长 (更优雅)
  // DJ 模式下保留更强节拍响应，用户拖动时降低空闲漂移。
  var dj = djMode.active;
  var shake = clampRange(Number(fx.cinemaShake) || 0, 0, 1.8);
  var beatDamp = (orbit.focus.active ? (dj ? 0.66 : 0.55) : (dj ? 1.12 : 1.0)) * shake;
  var idleDamp = damp * (dj ? 0.72 : 1.0) * shake;
  orbit.cineTheta  = Math.sin(cinemaT * 0.08) * 0.012 * idleDamp + beatCam.thetaKick * beatDamp;
  orbit.cinePhi    = Math.sin(cinemaT * 0.06 + 1.0) * 0.010 * idleDamp + beatCam.phiKick * beatDamp;
  orbit.cineRadius = Math.sin(cinemaT * 0.04 + 2.0) * 0.080 * idleDamp - beatCam.radiusKick * beatDamp * (dj ? 1.22 : 1.18);
}
// 初始化后立即计算一次相机位置，避免首帧相机未就位。
updateCamera();

// 将视角回到中心并清理所有焦点、粒子旋转和骷髅缩放状态。
function recenterCamera() {
  // 中心锁让后续 updateCamera 使用 baseline 姿态。
  orbit.centerLocked = true;
  orbit.recentering = true;
  clearCenteredViewOffsets();
  if (typeof skullWheelZoomTarget !== 'undefined') {
    // 骷髅滚轮缩放也回到默认值。
    skullWheelZoomTarget = 0;
    if (!(fx && fx.preset === SKULL_PRESET_INDEX)) skullWheelZoom = 0;
  }
  // 同时解除任何镜头跟拍
  if (focusHover) {
    focusHover.wantType = null;
    if (focusHover.pendingTimer) { clearTimeout(focusHover.pendingTimer); focusHover.pendingTimer = null; }
    if (focusHover.exitTimer) { clearTimeout(focusHover.exitTimer); focusHover.exitTimer = null; }
  }
  orbit.focus.active = false;
  if (fx && fx.preset === SKULL_PRESET_INDEX) {
    // 骷髅预设使用专用视角回正逻辑。
    resetSkullPresetView(false, { smooth:true, keepLyricLock:true });
  } else {
    resetSkullPresetView(true);
  }
  if (!(fx && fx.preset === SKULL_PRESET_INDEX) && ((fx && fx.lyricCameraLock) || shouldUseWallpaperLyricCameraLock())) requestStageLyricCameraSnap(14);
  showToast('视角回正');
}

// 判断当前是否存在可交互的播放控制上下文。
function hasActivePlaybackControls() {
  return !!(playing || (audio && !audio.paused) || (Array.isArray(playQueue) && currentIdx >= 0 && playQueue[currentIdx]));
}

// 设置底部控制条软隐藏状态。
function setControlsHidden(hidden) {
  var bar = document.getElementById('bottom-bar');
  if (!bar) return;
  // 鼠标悬停或迷你队列打开时禁止隐藏。
  if (hidden && (controlsHovering || miniQueueOpen)) hidden = false;
  bar.classList.toggle('soft-hidden', !!hidden && controlsAutoHide && bar.classList.contains('visible'));
  bar.style.pointerEvents = '';
  updateControlsChromeState();
}

// 判断底部控制条是否被歌单架交互临时抑制。
function isBottomControlsSuppressedForShelf() {
  // 读取 shelfManager 时加 try，避免模块初始化顺序导致异常。
  var shelfContentOpen = false;
  try {
    shelfContentOpen = !!(typeof shelfManager !== 'undefined' && shelfManager && shelfManager.hasOpenContent && shelfManager.hasOpenContent());
  } catch (e) {}
  return !!(shelfPinnedOpen || shelfContentOpen || (controlsShelfSuppressUntil && performance.now() < controlsShelfSuppressUntil));
}

// 歌单架打开或交互时临时隐藏底部控制条。
function suppressBottomControlsForShelf(duration) {
  // suppressUntil 让鼠标移动短时间内也不会重新唤出控制条。
  controlsShelfSuppressUntil = performance.now() + (duration == null ? 900 : duration);
  controlsHovering = false;
  if (controlsHideTimer) {
    clearTimeout(controlsHideTimer);
    controlsHideTimer = null;
  }
  if (miniQueueOpen) closeMiniQueue();
  var bar = document.getElementById('bottom-bar');
  if (bar) {
    bar.classList.remove('visible', 'soft-hidden');
    bar.style.pointerEvents = '';
  }
  updateControlsChromeState();
}

// 安排控制条在延迟后软隐藏。
function scheduleControlsHide(delay) {
  if (controlsHideTimer) clearTimeout(controlsHideTimer);
  // 自动隐藏关闭时不排隐藏任务。
  if (!controlsAutoHide) return;
  controlsHideTimer = setTimeout(function(){
    controlsHideTimer = null;
    if (!controlsHovering) setControlsHidden(true);
  }, delay == null ? 480 : delay);
}

// 显示底部控制条，并按自动隐藏设置安排隐藏。
function revealBottomControls(delay) {
  var bar = document.getElementById('bottom-bar');
  // 歌单架抑制期间不显示底部控制条。
  if (isBottomControlsSuppressedForShelf()) return;
  if (bar) bar.classList.add('visible');
  setControlsHidden(false);
  if (controlsAutoHide) scheduleControlsHide(delay == null ? 520 : delay);
}

// 同步 body 的控制条可见状态类名。
function updateControlsChromeState() {
  var bar = document.getElementById('bottom-bar');
  var active = !!(bar && bar.classList.contains('visible') && !bar.classList.contains('soft-hidden'));
  document.body.classList.toggle('controls-visible', active);
}


// 强制恢复播放控制按钮的可交互状态。
function forcePlaybackControlsInteractive() {
  // 没有播放上下文时不强制显示控制条。
  if (!hasActivePlaybackControls()) return;
  try {
    var bar = document.getElementById('bottom-bar');
    if (bar) {
      bar.style.pointerEvents = '';
      if (!controlsAutoHide) {
        bar.classList.add('visible');
        bar.classList.remove('soft-hidden');
      }
    }
    ['play-btn', 'prev-btn', 'next-btn', 'mini-queue-btn', 'play-mode-btn'].forEach(function(id){
      // 清掉可能残留的 busy/disabled，避免宿主桥接命令失败后按钮卡住。
      var btn = document.getElementById(id);
      if (!btn) return;
      btn.disabled = false;
      btn.classList.remove('busy');
    });
    updateControlsChromeState();
    if (bar && bar.classList.contains('visible') && controlsAutoHide && !controlsHovering) scheduleControlsHide(220);
  } catch (e) {
    console.warn('[PlaybackControlsRestore]', e);
  }
}

// 根据指针位置更新控制条自动隐藏状态。
function updateControlsAutoHideFromPointer(x, y) {
  if (isBottomControlsSuppressedForShelf()) return;
  var bar = document.getElementById('bottom-bar');
  if (!bar || !bar.classList.contains('visible')) return;
  if (!controlsAutoHide) { setControlsHidden(false); return; }
  var fxPanel = document.getElementById('fx-panel');
  var fxFab = document.getElementById('fx-fab');
  var fr = fxPanel ? fxPanel.getBoundingClientRect() : null;
  var br = fxFab ? fxFab.getBoundingClientRect() : null;
  var overFxPanel = fxPanel && (fxPanel.classList.contains('peek') || fxPanel.classList.contains('show')) && fr && x >= fr.left - 18 && x <= fr.right + 18 && y >= fr.top - 18 && y <= fr.bottom + 18;
  var overFxFab = br && x >= br.left - 18 && x <= br.right + 18 && y >= br.top - 18 && y <= br.bottom + 18;
  if (overFxPanel || overFxFab) {
    scheduleControlsHide(80);
    return;
  }
  controlsLastMoveAt = performance.now();
  var rect = bar.getBoundingClientRect();
  var overBar = x >= rect.left - 18 && x <= rect.right + 18 && y >= rect.top - 18 && y <= rect.bottom + 14;
  var mini = document.getElementById('mini-queue-popover');
  var miniRect = mini ? mini.getBoundingClientRect() : null;
  var overMini = miniQueueOpen && miniRect && x >= miniRect.left - 16 && x <= miniRect.right + 16 && y >= miniRect.top - 16 && y <= miniRect.bottom + 16;
  if (overBar || overMini) revealBottomControls(520);
  else scheduleControlsHide(70);
}

// 切换底部控制条自动隐藏偏好。
function toggleControlsAutoHide() {
  controlsAutoHide = !controlsAutoHide;
  // 用户偏好立即持久化。
  saveBooleanPreference(CONTROLS_AUTO_HIDE_STORE_KEY, controlsAutoHide);
  var btn = document.getElementById('controls-hide-btn');
  if (btn) btn.classList.toggle('active', controlsAutoHide);
  setControlsHidden(false);
  if (controlsAutoHide) {
    scheduleControlsHide(520);
    showToast('控制条自动隐藏已开启');
  } else {
    if (controlsHideTimer) { clearTimeout(controlsHideTimer); controlsHideTimer = null; }
    showToast('控制条保持显示');
  }
}

// 将已保存的自动隐藏偏好同步到按钮和当前控制条状态。
function applyControlsAutoHidePreference() {
  var btn = document.getElementById('controls-hide-btn');
  if (btn) btn.classList.toggle('active', !!controlsAutoHide);
  if (!controlsAutoHide && controlsHideTimer) {
    clearTimeout(controlsHideTimer);
    controlsHideTimer = null;
  }
  setControlsHidden(false);
}

// 初始化控制条悬停、离开事件。
(function initControlsAutoHide() {
  var bar = document.getElementById('bottom-bar');
  if (!bar) return;
  // 进入控制条区域时保持显示并取消隐藏计时器。
  function enterControls(){
    controlsHovering = true;
    setControlsHidden(false);
    if (controlsHideTimer) { clearTimeout(controlsHideTimer); controlsHideTimer = null; }
  }
  // 离开控制条区域时按自动隐藏策略收起。
  function leaveControls(){
    controlsHovering = false;
    scheduleControlsHide(70);
  }
  bar.addEventListener('mouseenter', enterControls);
  bar.addEventListener('mouseleave', leaveControls);
  updateControlsChromeState();
})();

// 判断当前是否允许鼠标指针自动隐藏。
function isCursorAutoHideMode() {
  return !document.hidden;
}

// 清理鼠标自动隐藏计时器。
function clearCursorAutoHideTimer() {
  if (cursorHideTimer) {
    clearTimeout(cursorHideTimer);
    cursorHideTimer = null;
  }
}

// 设置 body 上的鼠标隐藏类名。
function setCursorHidden(hidden) {
  document.body.classList.toggle('cursor-hidden', !!hidden && isCursorAutoHideMode());
}

// 安排鼠标指针在一段时间无活动后隐藏。
function scheduleCursorHide(delay) {
  clearCursorAutoHideTimer();
  if (!isCursorAutoHideMode()) {
    // 页面隐藏时强制显示状态，避免恢复后指针仍隐藏。
    setCursorHidden(false);
    return;
  }
  cursorHideTimer = setTimeout(function(){
    cursorHideTimer = null;
    setCursorHidden(true);
  }, delay == null ? CURSOR_HIDE_DELAY : delay);
}

// 用户发生鼠标、滚轮或触控活动时显示指针并重新计时。
function revealCursorForActivity() {
  if (!isCursorAutoHideMode()) {
    clearCursorAutoHideTimer();
    setCursorHidden(false);
    return;
  }
  setCursorHidden(false);
  scheduleCursorHide(CURSOR_HIDE_DELAY);
}

// 根据当前页面可见性同步鼠标自动隐藏模式。
function syncCursorAutoHideMode() {
  if (isCursorAutoHideMode()) revealCursorForActivity();
  else {
    clearCursorAutoHideTimer();
    setCursorHidden(false);
  }
}

// 这些全局输入都会唤醒鼠标指针。
['mousemove', 'pointermove', 'mousedown', 'wheel', 'touchstart'].forEach(function(type){
  window.addEventListener(type, revealCursorForActivity, { passive:true, capture:true });
});
syncCursorAutoHideMode();

// ============================================================
//  指针 / 拖拽控制
//   v7.1: 用 userOrbit 替代 targetOrbit; 加 drag 距离判断
// ============================================================
// 当前鼠标在粒子平面上的本地坐标，默认放到远处表示无效。
var mouseWorld = new THREE.Vector3(-999, -999, 0);
// 鼠标是否当前命中粒子交互平面。
var mouseActive = false;
// 鼠标按下位置、时间和是否发生拖拽，用于区分点击与拖动。
var mouseDownAt = { x:0, y:0, t:0, hadDrag:false };
// 粒子拖拽旋转的上一帧指针状态。
var particlePointerSpin = { active:false, lastX:0, lastY:0, lastT:0 };
// 粒子指针命中检测复用对象，避免每次鼠标移动都分配新对象。
var particlePointerRay = new THREE.Raycaster();
var particlePointerNdc = new THREE.Vector2();
var particlePointerPlane = new THREE.Plane();
var particlePointerPlanePoint = new THREE.Vector3();
var particlePointerPlaneNormal = new THREE.Vector3();
var particlePointerWorldHit = new THREE.Vector3();
var particlePointerLocalHit = new THREE.Vector3();
var particlePointerQuat = new THREE.Quaternion();
// 鼠标移动只写入这一帧缓存，主循环再统一计算命中，降低事件处理成本。
var particlePointerFrame = { dirty:false, ndcX:0, ndcY:0 };
// 鼠标按下后移动超过该像素距离视为拖拽，不再触发点击动作。
var CLICK_THRESHOLD = 6;  // 像素, 拖动 > 6px 视为 drag
// 这些 UI 区域会阻止画布拖拽和粒子交互。
var UI_HIT_SELECTOR = '#top-right,#fx-panel,#fx-fab,#playlist-panel,#bottom-bar,#thumb-wrap,.modal-mask,#toast,#ai-depth-chip,#beat-chip';

// 判断指针是否位于播放器 UI 控件上。
function isPointerOverUi(e) {
  if (!e) return false;
  var el = document.elementFromPoint(e.clientX, e.clientY);
  return !!(el && el.closest && el.closest(UI_HIT_SELECTOR));
}

// 把 NDC 坐标投射到粒子所在平面，输出粒子本地坐标。
function particleLocalPointFromNdc(ndcX, ndcY, out) {
  // 先用主相机生成射线。
  particlePointerNdc.set(ndcX, ndcY);
  particlePointerRay.setFromCamera(particlePointerNdc, camera);
  if (particles) {
    // 粒子存在时使用粒子当前世界位置和朝向构造命中平面。
    particles.updateMatrixWorld(true);
    particles.getWorldPosition(particlePointerPlanePoint);
    particles.getWorldQuaternion(particlePointerQuat);
    particlePointerPlaneNormal.set(0, 0, 1).applyQuaternion(particlePointerQuat).normalize();
    if (Math.abs(particlePointerPlaneNormal.dot(particlePointerRay.ray.direction)) < 0.16) return false;
    particlePointerPlane.setFromNormalAndCoplanarPoint(particlePointerPlaneNormal, particlePointerPlanePoint);
    if (particlePointerRay.ray.intersectPlane(particlePointerPlane, particlePointerWorldHit)) {
      // 命中世界坐标转为粒子本地坐标，shader 鼠标交互使用本地坐标。
      out.copy(particlePointerWorldHit);
      particles.worldToLocal(out);
      return isFinite(out.x) && isFinite(out.y) && Math.abs(out.x) < 8.5 && Math.abs(out.y) < 8.5;
    }
  }
  // 粒子尚未创建时退回 z=0 平面，保证启动早期也有基本交互。
  particlePointerPlaneNormal.set(0, 0, 1);
  particlePointerPlane.set(particlePointerPlaneNormal, 0);
  if (particlePointerRay.ray.intersectPlane(particlePointerPlane, particlePointerWorldHit)) {
    out.copy(particlePointerWorldHit);
    return isFinite(out.x) && isFinite(out.y) && Math.abs(out.x) < 8.5 && Math.abs(out.y) < 8.5;
  }
  return false;
}

// 将屏幕坐标写入待处理的粒子指针帧。
function queueParticlePointerFrame(clientX, clientY) {
  // 转换为 WebGL NDC 坐标。
  var mx = (clientX / innerWidth) * 2 - 1;
  var my = -(clientY / innerHeight) * 2 + 1;
  pointerTarget.x = mx; pointerTarget.y = my;
  particlePointerFrame.ndcX = mx;
  particlePointerFrame.ndcY = my;
  particlePointerFrame.dirty = true;
}

// 主循环中消费待处理的粒子指针帧，并更新 mouseWorld/mouseActive。
function updateParticlePointerFrame() {
  if (!particlePointerFrame.dirty) return;
  particlePointerFrame.dirty = false;
  if (particleLocalPointFromNdc(particlePointerFrame.ndcX, particlePointerFrame.ndcY, particlePointerLocalHit)) {
    // 命中粒子平面时把坐标写给 shader uniform。
    mouseWorld.x = particlePointerLocalHit.x;
    mouseWorld.y = particlePointerLocalHit.y;
    mouseActive = true;
  } else {
    // 未命中时放到远处，shader 会视为没有鼠标交互。
    mouseWorld.set(-999, -999, 0);
    mouseActive = false;
  }
}

// 开始粒子/轨道拖拽。
function beginParticlePointerDrag(e) {
  // 右键不进入拖拽。
  if (e.button === 2) return;
  // UI 上的点击不应该拖动画布。
  if (isPointerOverUi(e)) return;
  markRenderInteraction('canvas-drag', 1200);
  // 空闲引导也需要收到按下事件，用于关闭或反馈。
  idleGuidePointerDown(e);
  orbit.rotating = true; orbit.last.x = e.clientX; orbit.last.y = e.clientY;
  particlePointerSpin.active = true;
  particlePointerSpin.lastX = e.clientX;
  particlePointerSpin.lastY = e.clientY;
  particlePointerSpin.lastT = performance.now();
  if (typeof particleSpin !== 'undefined') particleSpin.vx = particleSpin.vy = 0;
  // 记录按下点，后续判断是否超过点击阈值。
  mouseDownAt.x = e.clientX; mouseDownAt.y = e.clientY;
  mouseDownAt.t = performance.now(); mouseDownAt.hadDrag = false;
}
// 画布自身按下直接开始拖拽。
renderer.domElement.addEventListener('mousedown', function(e){
  beginParticlePointerDrag(e);
});
// 骷髅预设下允许从窗口其他非 UI 区域开始拖拽。
window.addEventListener('mousedown', function(e){
  if (!(fx && fx.preset === SKULL_PRESET_INDEX)) return;
  if (orbit.rotating || e.target === renderer.domElement) return;
  beginParticlePointerDrag(e);
}, true);
// 全局鼠标移动：同时驱动控制条、自由相机、粒子拖拽和鼠标命中。
window.addEventListener('mousemove', function(e){
  updateControlsAutoHideFromPointer(e.clientX, e.clientY);
  idleGuidePointerMove(e);
  if (freeCamera && freeCamera.active) {
    // 自由相机激活时鼠标移动只控制相机视角。
    markRenderInteraction('free-camera', 900);
    var mdx = e.movementX || 0;
    var mdy = e.movementY || 0;
    if ((!mdx && !mdy) && freeCameraPointer.seen) {
      // 没有 movementX/Y 时用前后 clientX/Y 差值兜底。
      mdx = e.clientX - freeCameraPointer.x;
      mdy = e.clientY - freeCameraPointer.y;
    }
    freeCameraPointer.x = e.clientX;
    freeCameraPointer.y = e.clientY;
    freeCameraPointer.seen = true;
    freeCamera.yaw -= mdx * 0.00125;
    freeCamera.pitch = clampRange(freeCamera.pitch - mdy * 0.00125, -Math.PI * 0.49, Math.PI * 0.49);
    return;
  }
  if (isPointerOverUi(e) && !orbit.rotating) { mouseActive = false; return; }
  if (orbit.rotating) {
    // 正在拖拽时更新粒子旋转惯性。
    markRenderInteraction('canvas-drag', 900);
    unlockCenteredView();
    var dx = e.clientX - orbit.last.x, dy = e.clientY - orbit.last.y;
    if (particlePointerSpin.active) {
      // 用移动距离和时间间隔估算拖拽角速度。
      var nowSpin = performance.now();
      var spinDt = Math.max(1 / 120, Math.min(0.08, (nowSpin - particlePointerSpin.lastT) / 1000 || 1 / 60));
      applyParticleSpinDrag(dx, dy, spinDt);
      particlePointerSpin.lastX = e.clientX;
      particlePointerSpin.lastY = e.clientY;
      particlePointerSpin.lastT = nowSpin;
    }
    orbit.last.x = e.clientX; orbit.last.y = e.clientY;
    // drag 距离判断
    var totalDx = e.clientX - mouseDownAt.x, totalDy = e.clientY - mouseDownAt.y;
    if (Math.sqrt(totalDx*totalDx + totalDy*totalDy) > CLICK_THRESHOLD) mouseDownAt.hadDrag = true;
    if (orbit.recentering) orbit.recentering = false;
  }
  queueParticlePointerFrame(e.clientX, e.clientY);
});
// 鼠标释放时结束所有由按下触发的画布拖拽状态。
window.addEventListener('mouseup', function(){
  // 轨道拖拽停止后，后续 mousemove 不再改变相机或粒子惯性。
  orbit.rotating = false;
  // 粒子旋转惯性采样也同步关闭，避免释放后继续写入拖拽速度。
  particlePointerSpin.active = false;
  // 空闲引导需要收到释放事件，用于恢复提示状态或完成点击判断。
  idleGuidePointerUp();
});
// 鼠标离开画布时清理粒子命中状态，避免 shader 继续使用旧坐标。
renderer.domElement.addEventListener('mouseleave', function(){
  // 丢弃尚未被主循环消费的指针帧。
  particlePointerFrame.dirty = false;
  // 把鼠标位置移到远处，让 shader 中的交互距离判断自然失效。
  mouseWorld.set(-999, -999, 0);
  // 标记鼠标已不再作用于粒子平面。
  mouseActive = false;
  // 通知空闲引导鼠标已经离开主舞台区域。
  idleGuidePointerLeave();
});
// 鼠标滚轮在画布上负责缩放当前视觉视角。
renderer.domElement.addEventListener('wheel', function(e){
  // UI 控件上的滚轮操作交给控件自身处理。
  if (isPointerOverUi(e)) return;
  // 阻止页面滚动，确保滚轮只改变 3D 视图。
  e.preventDefault();
  // 滚轮交互期间提高渲染活跃度，避免降帧影响反馈。
  markRenderInteraction('canvas-wheel', 900);
  if (freeCamera && freeCamera.active) {
    // 自由相机模式下滚轮调整视场角，而不是改变轨道半径。
    freeCamera.fov = clampRange((freeCamera.fov || BASE_FOV) + e.deltaY * 0.018, 26, 72);
    // 视场角属于自由相机偏好，立即持久化。
    saveFreeCameraState();
    return;
  }
  if (fx && fx.preset === SKULL_PRESET_INDEX && typeof skullWheelZoomTarget !== 'undefined') {
    // 骷髅预设使用专属缩放目标，避免和通用轨道半径互相覆盖。
    skullWheelZoomTarget = clampRange(skullWheelZoomTarget + e.deltaY * 0.00155, -0.95, 1.28);
    return;
  }
  // 其它预设下滚轮同时唤醒空闲引导和解除居中锁定。
  idleGuideWheel(e);
  unlockCenteredView();
  // 轨道相机半径限制在预设允许范围内，防止穿过或远离舞台。
  orbit.userRadius = Math.max(orbit.minRadius, Math.min(orbit.maxRadius, orbit.userRadius + e.deltaY * 0.005));
  // 用户手动缩放后取消自动回正动画。
  if (orbit.recentering) orbit.recentering = false;
}, { passive:false });

// 双击屏幕回正 — 不命中卡片时
renderer.domElement.addEventListener('dblclick', function(e){
  // 双击 UI 时不触发舞台回正。
  if (isPointerOverUi(e)) return;
  if (freeCamera && freeCamera.locked) {
    // 自由相机锁定状态下双击优先恢复自由相机默认姿态。
    resetFreeCameraToDefault();
    // 骷髅预设同步重置视图，但保留歌词锁定语义。
    resetSkullPresetView(false, { smooth:true, keepLyricLock:true });
    return;
  }
  if (shelfManager && shelfManager.getMode() !== 'off') {
    // 歌单架开启时，先判断双击是否落在卡片上。
    var mx = (e.clientX / innerWidth) * 2 - 1;
    // 屏幕 Y 轴需要翻转为 Three.js 标准化设备坐标。
    var my = -(e.clientY / innerHeight) * 2 + 1;
    // 临时射线只用于本次双击命中测试。
    var rc = new THREE.Raycaster();
    rc.setFromCamera(new THREE.Vector2(mx, my), camera);
    // 命中卡片时让卡片交互接管，不做舞台回正。
    if (shelfManager.raycastCards(rc)) return;
  }
  // 没有命中 UI 或卡片时恢复主视觉相机。
  recenterCamera();
});



// ===== js/02-particle-systems.js =====

// ============================================================
//  粒子点纹理 (干净圆点, 无 glow)
// ============================================================
function makeDotTexture() {
  // 使用小尺寸 canvas 生成点精灵贴图，避免依赖外部图片资源。
  var cv = document.createElement('canvas'); cv.width = cv.height = 64;
  // 2D 上下文用于绘制中心亮、边缘透明的径向渐变。
  var ctx = cv.getContext('2d');
  // 渐变半径覆盖整个点精灵，让片元 shader 能得到柔和圆点。
  var g = ctx.createRadialGradient(32, 32, 0, 32, 32, 31);
  g.addColorStop(0.00, 'rgba(255,255,255,0.96)');
  g.addColorStop(0.42, 'rgba(255,255,255,0.78)');
  g.addColorStop(0.72, 'rgba(255,255,255,0.22)');
  g.addColorStop(1.00, 'rgba(255,255,255,0)');
  ctx.fillStyle = g;
  ctx.fillRect(0, 0, 64, 64);
  // CanvasTexture 直接作为 PointsMaterial/ShaderMaterial 的点纹理。
  var tex = new THREE.CanvasTexture(cv);
  // 线性过滤让点大小变化时边缘更平滑。
  tex.minFilter = THREE.LinearFilter; tex.magFilter = THREE.LinearFilter;
  return tex;
}
// 全局点精灵纹理，主粒子和辉光粒子共用。
var dotTexture = makeDotTexture();

// ============================================================
//  主粒子系统
//   - 5 个 preset, 每个预设走完全不同的 pos 计算
//   - 共享: 封面色采样, 鼠标交互, 粒子大小限制
// ============================================================
// SILK 平面预设的基础正方形尺寸，几何坐标会映射到这个范围。
var PLANE_SIZE = 4.8;
// 同时保留的鼠标涟漪数量上限，shader 中循环次数也按这个值固定。
var RIPPLE_MAX = 12;

// 当前封面粒子网格宽度；高度与宽度一致，形成正方形采样网格。
var GRID_X = coverParticleGridForResolution(fx.coverResolution), GRID_Y = GRID_X;
// 当前粒子总数，供后续统计和材质逻辑引用。
var PCOUNT = GRID_X * GRID_Y;
// 当前几何体的 typed array 引用，重建分辨率时会同步替换。
var positions = null, uvs = null, aRand = null;
// 分辨率切换后的封面重载定时器，用于合并连续调整。
var coverResolutionReloadTimer = null;
// 记录当前封面来源，粒子分辨率变更后用它重新套用封面。
var currentCoverSource = null;
// 复用的封面取色 canvas，避免每次采样都新建画布。
var coverPickerCanvas = null;

// 根据目标网格尺寸重新生成封面粒子几何。
function buildCoverParticleGeometry(grid) {
  // 调用方可能传入历史网格值，这里统一映射回受支持的封面分辨率档位。
  grid = coverParticleGridForResolution(grid / 118);
  // 粒子数量等于网格宽高相乘。
  var count = grid * grid;
  // 新几何体承载 position、aUv 和 aRand 三组属性。
  var nextGeo = new THREE.BufferGeometry();
  // 顶点位置数组，三个浮点数表示一个粒子的本地坐标。
  var nextPositions = new Float32Array(count * 3);
  // 封面采样 UV 数组，两个浮点数表示一个粒子的纹理坐标。
  var nextUvs = new Float32Array(count * 2);
  // 每粒子的随机种子，用于 shader 中制造细微差异。
  var nextRand = new Float32Array(count);
  // 每个网格单元在 UV 空间中的步长。
  var texelStep = 1 / grid;
  for (var i = 0; i < count; i++) {
    // 当前粒子在二维网格中的列和行。
    var gx = i % grid, gy = Math.floor(i / grid);
    // 采样点放在像素格中心，减少边缘采样偏移。
    var u = (gx + 0.5) * texelStep, v = (gy + 0.5) * texelStep;
    // 将网格坐标归一化到 0..1，用于映射到本地平面。
    var px = gx / (grid - 1), py = gy / (grid - 1);
    nextPositions[i*3]   = (px - 0.5) * PLANE_SIZE;
    nextPositions[i*3+1] = (py - 0.5) * PLANE_SIZE;
    nextPositions[i*3+2] = 0;
    nextUvs[i*2]   = u;
    nextUvs[i*2+1] = v;
    nextRand[i]   = Math.random();
  }
  nextGeo.setAttribute('position', new THREE.BufferAttribute(nextPositions, 3));
  nextGeo.setAttribute('aUv',      new THREE.BufferAttribute(nextUvs, 2));
  nextGeo.setAttribute('aRand',    new THREE.BufferAttribute(nextRand, 1));
  // 在 userData 上记录网格信息，便于后续判断是否真的需要重建。
  nextGeo.userData.grid = grid;
  nextGeo.userData.count = count;
  // 同步更新模块级数组引用，供其它运行期逻辑读取最新几何数据。
  positions = nextPositions;
  uvs = nextUvs;
  aRand = nextRand;
  return nextGeo;
}

// 初始粒子几何，后续分辨率变化会替换这个引用。
var geo = buildCoverParticleGeometry(GRID_X);

// 应用封面粒子分辨率设置，并按需重建几何和重载封面。
function applyCoverParticleResolution(value, opts) {
  // opts.reload=false 时只换几何，不触发封面重载。
  opts = opts || {};
  // 先把用户输入归一化为合法分辨率档位。
  fx.coverResolution = normalizeCoverResolution(value);
  // 档位再映射为实际网格尺寸。
  var grid = coverParticleGridForResolution(fx.coverResolution);
  // 如果网格没有变化，直接返回，避免无意义释放和重建 GPU 资源。
  if (grid === GRID_X && geo && geo.userData && geo.userData.grid === grid) return;
  // 保留旧几何，替换成功后再释放。
  var oldGeo = geo;
  // 生成下一版几何。
  var nextGeo = buildCoverParticleGeometry(grid);
  geo = nextGeo;
  // 同步全局网格尺寸和粒子数量。
  GRID_X = GRID_Y = grid;
  PCOUNT = grid * grid;
  // 主粒子和辉光粒子共享同一套几何，因此需要一起替换。
  if (particles) particles.geometry = nextGeo;
  if (bloomParticles) bloomParticles.geometry = nextGeo;
  // 释放旧 BufferGeometry，避免分辨率反复切换造成显存泄漏。
  if (oldGeo && oldGeo !== nextGeo) oldGeo.dispose();
  // 分辨率切换时给视觉一个轻微脉冲，掩盖采样密度变化。
  uniforms.uBurstAmt.value = Math.max(uniforms.uBurstAmt.value, 0.18);
  // 默认重新载入当前封面，让新粒子密度使用最新采样。
  if (opts.reload !== false) scheduleCoverResolutionReload();
}

// 延迟重载当前封面，合并连续的分辨率调整。
function scheduleCoverResolutionReload() {
  // 没有封面来源时没有可重载内容。
  if (!currentCoverSource || !currentCoverSource.src) return;
  // 取消上一轮排队，确保只执行最后一次调整。
  if (coverResolutionReloadTimer) clearTimeout(coverResolutionReloadTimer);
  coverResolutionReloadTimer = setTimeout(function(){
    // 定时器触发后清空句柄，便于后续重新排队。
    coverResolutionReloadTimer = null;
    // 执行前再次确认封面来源仍然存在。
    if (!currentCoverSource || !currentCoverSource.src) return;
    if (currentCoverSource.kind === 'url') {
      // URL 封面走图片加载流程，并带上当前曲目 token 防止串歌。
      loadCoverFromUrl(currentCoverSource.src, { trackToken: trackSwitchToken, fromResolutionChange: true });
    } else if (currentCoverSource.kind === 'data') {
      // data URL 封面直接应用，同样携带 token 标记来源。
      applyCoverDataUrl(currentCoverSource.src, { trackToken: trackSwitchToken, fromResolutionChange: true });
    }
  }, 260);
}

// 涟漪数据纹理 (1×N, RGBA: x, y, age, str)
// 每个涟漪占四个浮点数，shader 会按 DataTexture 逐行读取。
var rippleData = new Float32Array(RIPPLE_MAX * 4);
// DataTexture 把 CPU 侧涟漪状态传入 shader。
var rippleTex  = new THREE.DataTexture(rippleData, 1, RIPPLE_MAX, THREE.RGBAFormat, THREE.FloatType);
// 最近邻过滤保证每个涟漪槽位不会被相邻行插值污染。
rippleTex.magFilter = THREE.NearestFilter; rippleTex.minFilter = THREE.NearestFilter;
// JavaScript 侧的涟漪对象池，用于更新 age、强度和坐标。
var ripples = [];
// 初始化固定数量的涟漪槽位，age 为负表示空闲。
for (var ri = 0; ri < RIPPLE_MAX; ri++) ripples.push({ x:0, y:0, age:-10, str:0 });

// 封面纹理 + 边缘/深度纹理
// 当前封面颜色纹理，主 shader 通过它给粒子取色。
var coverTex = new THREE.Texture();
// 封面纹理夹边，避免采样到透明边或重复边缘。
coverTex.minFilter = THREE.LinearFilter; coverTex.magFilter = THREE.LinearFilter;
coverTex.wrapS = THREE.ClampToEdgeWrapping; coverTex.wrapT = THREE.ClampToEdgeWrapping;

// 当前封面的深度、边缘、前景遮罩和亮度纹理。
var coverEdgeTex = new THREE.Texture();  // R=depth, G=edge, B=fg-mask, A=lum
// 深度/边缘贴图使用线性过滤，让位移和亮度过渡更平滑。
coverEdgeTex.minFilter = THREE.LinearFilter; coverEdgeTex.magFilter = THREE.LinearFilter;

// 初始 1×1 像素
(function(){
  // 在真实封面加载前提供占位颜色，避免 shader 采样空纹理。
  var c = document.createElement('canvas'); c.width = c.height = 4;
  // 占位封面使用深色底，启动阶段不会闪白。
  var x = c.getContext('2d'); x.fillStyle = '#1c1c28'; x.fillRect(0,0,4,4);
  coverTex.image = c; coverTex.needsUpdate = true;
  // 深度占位纹理使用中性深度值，避免初始画面产生夸张位移。
  var d = document.createElement('canvas'); d.width = d.height = 4;
  // R 通道 128 表示中性深度，其他通道保持关闭或低影响。
  var dx = d.getContext('2d'); dx.fillStyle = 'rgba(128,0,0,255)'; dx.fillRect(0,0,4,4);
  coverEdgeTex.image = d; coverEdgeTex.needsUpdate = true;
})();

// 前一首封面纹理 (用于切歌渐变)
// 切歌时保留上一张封面，shader 可以在新旧封面之间混合。
var prevCoverTex = new THREE.Texture();
// 前一首封面同样使用线性过滤，保证过渡期间采样一致。
prevCoverTex.minFilter = THREE.LinearFilter; prevCoverTex.magFilter = THREE.LinearFilter;
(function(){
  // 初始上一首封面也使用深色占位，避免第一次切换前采样为空。
  var c = document.createElement('canvas'); c.width = c.height = 4;
  // 占位上下文只负责填充固定底色。
  var x = c.getContext('2d'); x.fillStyle = '#1c1c28'; x.fillRect(0,0,4,4);
  prevCoverTex.image = c; prevCoverTex.needsUpdate = true;
})();

// shader 统一变量集中定义在这里：
// 音频能量、封面纹理、深度纹理、鼠标状态、预设切换和加载态都会从主循环或封面管线写入。
// 新增视觉效果时优先复用这些 uniform，避免在 shader 和 JavaScript 之间散落多套状态。
var uniforms = {
  // 全局动画时间，主循环持续写入。
  uTime:       { value: 0 },
  // 低频能量，主要驱动呼吸、缩放和重低音脉冲。
  uBass:       { value: 0 },
  // 中频能量，主要驱动丝绸起伏和流动细节。
  uMid:        { value: 0 },
  // 高频能量，主要驱动闪烁、细碎扰动和颗粒亮度。
  uTreble:     { value: 0 },
  // 节拍瞬时强度，用于让预设在鼓点上产生短促响应。
  uBeat:       { value: 0 },
  // 综合音频能量，作为全局亮度和活跃度参考。
  uEnergy:     { value: 0 },
  // 预设切换或重载时的通用爆发量。
  uBurstAmt:   { value: 0 },          // 通用预设切换脉冲 0..1
  // 黑胶预设的唱片自旋角度。
  uVinylSpin:  { value: 0 },
  // 当前视觉预设索引，shader 通过区间判断走不同分支。
  uPreset:     { value: 0 },
  // 视觉强度滑块，放大音频位移和扰动。
  uIntensity:  { value: 0.85 },
  // 深度位移强度，主要影响 AI 深度或边缘深度贴图。
  uDepth:      { value: 1.0 },
  // 点精灵全局缩放，控制粒子视觉尺寸。
  uPointScale: { value: 1.0 },
  // 动画速度倍率，用于统一加快或放慢时间。
  uSpeed:      { value: 1.0 },
  // 丝绸预设的扭曲强度。
  uTwist:      { value: 0 },
  // 封面颜色增强参数，影响颜色 gamma 变化。
  uColorBoost: { value: 1.1 },
  // 离散散射强度，用于让粒子产生轻微分散。
  uScatter:    { value: 0 },
  // 封面粒子分辨率档位，shader 用它做高分辨率保护。
  uCoverRes:   { value: 1.0 },
  // 背景压暗强度，深度可用时用于突出前景。
  uBgFade:     { value: 0.20 },
  // 辉光层透明强度。
  uBloomStrength:{ value: 0.62 },
  // 辉光层点大小倍率。
  uBloomSize:  { value: 2.65 },
  // 用户色调覆盖色。
  uTintColor:  { value: new THREE.Color('#9db8cf') },
  // 用户色调混合强度。
  uTintStrength:{ value: 0 },
  // 当前封面颜色纹理。
  uCoverTex:   { value: coverTex },
  // 上一首封面颜色纹理。
  uPrevCoverTex:{ value: prevCoverTex },
  // 新旧封面混合进度。
  uColorMixT:  { value: 1.0 },        // 0=显示旧封面 → 1=显示新封面
  // 深度/边缘/前景遮罩/亮度合并纹理。
  uEdgeTex:    { value: coverEdgeTex },
  // 鼠标涟漪数据纹理。
  uRippleTex:  { value: rippleTex },
  // 当前有效涟漪数量。
  uRippleCount:{ value: 0 },
  // 点精灵透明度纹理。
  uDotTex:     { value: dotTexture },
  // 是否已有真实封面，0 时使用默认渐变色。
  uHasCover:   { value: 0 },
  // 是否已有深度贴图。
  uHasDepth:   { value: 0 },
  // 是否启用边缘增强。
  uEdgeEnabled:{ value: 1 },
  // AI 深度增强权重。
  uAiBoost:    { value: 0 },          // AI 深度增益, 当 AI 接管时升至 1
  // 鼠标在粒子本地平面上的坐标。
  uMouseXY:    { value: new THREE.Vector2(-999, -999) },
  // 鼠标是否正在影响粒子。
  uMouseActive:{ value: 0 },
  // 当前 renderer 像素比，用于修正点大小。
  uPixel:      { value: renderer.getPixelRatio() },
  // 粒子整体透明度，启动淡入和隐藏时使用。
  uAlpha:      { value: 0 },          // 整体粒子透明度 (启动 fade-in)
  // 叠层打开时的粒子压暗系数。
  uParticleDim:{ value: 1 },          // 覆盖层打开时只压低粒子背景, 不影响 3D 卡片
  // 空场浮动粒子透明度。
  uFloatAlpha: { value: 0 },          // 空场/浮空粒子透明度
  // 加载态混合量。
  uLoading:    { value: 0 },          // 加载动画混合度 0..1 (1 = 完全聚成圆环)
};
// 安装与页面可见性、后台省电相关的渲染钩子。
installRenderPowerHooks();
// 立即根据当前状态应用一次渲染功耗策略。
applyRendererPowerMode();

// ----- 顶点 Shader -----
//   v7.1: 律动幅度 ×2.5, Tunnel 自旋, 虚空预设, 切歌颜色渐变
// 顶点 shader 负责粒子位置、封面采样、深度位移和节拍扰动；片元 shader 只接收这里传出的颜色与亮度信息。
var vs = `
precision highp float;
uniform float uTime, uBass, uMid, uTreble, uBeat, uEnergy, uBurstAmt;
uniform float uPreset, uIntensity, uDepth, uPointScale, uSpeed, uTwist;
uniform float uVinylSpin;
uniform float uColorBoost, uScatter, uCoverRes, uBgFade;
uniform float uHasCover, uHasDepth, uEdgeEnabled, uAiBoost;
uniform float uMouseActive, uPixel, uColorMixT, uLoading;
uniform sampler2D uCoverTex, uPrevCoverTex, uEdgeTex, uRippleTex;
uniform int uRippleCount;
uniform vec2 uMouseXY;
uniform vec3 uTintColor;
uniform float uTintStrength;
attribute vec2 aUv;
attribute float aRand;
varying vec3 vColor;
varying float vBright, vRipple, vEdgeBoost, vAlpha, vSourceLum;

#define PI 3.14159265359

vec3 mod289(vec3 x){return x-floor(x*(1.0/289.0))*289.0;}
vec4 mod289v(vec4 x){return x-floor(x*(1.0/289.0))*289.0;}
vec4 perm(vec4 x){return mod289v(((x*34.0)+1.0)*x);}
float snoise(vec3 v){
  const vec2 C=vec2(1.0/6.0,1.0/3.0);
  const vec4 D=vec4(0.0,0.5,1.0,2.0);
  vec3 i=floor(v+dot(v,C.yyy));
  vec3 x0=v-i+dot(i,C.xxx);
  vec3 g=step(x0.yzx,x0.xyz); vec3 l=1.0-g;
  vec3 i1=min(g.xyz,l.zxy); vec3 i2=max(g.xyz,l.zxy);
  vec3 x1=x0-i1+C.xxx;
  vec3 x2=x0-i2+C.yyy;
  vec3 x3=x0-D.yyy;
  i=mod289(i);
  vec4 p=perm(perm(perm(i.z+vec4(0.0,i1.z,i2.z,1.0))+i.y+vec4(0.0,i1.y,i2.y,1.0))+i.x+vec4(0.0,i1.x,i2.x,1.0));
  float n_=0.142857142857;
  vec3 ns=n_*D.wyz-D.xzx;
  vec4 j=p-49.0*floor(p*ns.z*ns.z);
  vec4 x_=floor(j*ns.z); vec4 y_=floor(j-7.0*x_);
  vec4 x=x_*ns.x+ns.yyyy; vec4 y=y_*ns.x+ns.yyyy;
  vec4 h=1.0-abs(x)-abs(y);
  vec4 b0=vec4(x.xy,y.xy); vec4 b1=vec4(x.zw,y.zw);
  vec4 s0=floor(b0)*2.0+1.0; vec4 s1=floor(b1)*2.0+1.0;
  vec4 sh=-step(h,vec4(0.0));
  vec4 a0=b0.xzyw+s0.xzyw*sh.xxyy; vec4 a1=b1.xzyw+s1.xzyw*sh.zzww;
  vec3 p0=vec3(a0.xy,h.x); vec3 p1=vec3(a0.zw,h.y); vec3 p2=vec3(a1.xy,h.z); vec3 p3=vec3(a1.zw,h.w);
  vec4 norm=inversesqrt(vec4(dot(p0,p0),dot(p1,p1),dot(p2,p2),dot(p3,p3)));
  p0*=norm.x; p1*=norm.y; p2*=norm.z; p3*=norm.w;
  vec4 m=max(0.6-vec4(dot(x0,x0),dot(x1,x1),dot(x2,x2),dot(x3,x3)),0.0);
  m=m*m;
  return 42.0*dot(m*m,vec4(dot(p0,x0),dot(p1,x1),dot(p2,x2),dot(p3,x3)));
}

float hash11(float p) {
  return fract(sin(p * 127.1) * 43758.5453123);
}

vec2 safeCoverUv(vec2 uv) {
  return clamp(uv, vec2(0.0012), vec2(0.9988));
}

vec3 sampleNewCoverColor(vec2 uv) {
  return texture2D(uCoverTex, safeCoverUv(uv)).rgb;
}

vec3 samplePrevCoverColor(vec2 uv) {
  return texture2D(uPrevCoverTex, safeCoverUv(uv)).rgb;
}

vec4 sampleEdgeColor(vec2 uv) {
  return texture2D(uEdgeTex, safeCoverUv(uv));
}

float rippleSumAt(vec2 p, out float maxAmp) {
  float sum = 0.0; maxAmp = 0.0;
  for (int ri = 0; ri < 12; ri++) {
    if (ri >= uRippleCount) break;
    float vCoord = (float(ri) + 0.5) / 12.0;
    vec4 rd = texture2D(uRippleTex, vec2(0.5, vCoord));
    float age = rd.z; float str = rd.w;
    if (str < 0.005 || age < 0.0 || age > 2.0) continue;
    float dx = p.x - rd.x, dy = p.y - rd.y;
    float dist = sqrt(dx*dx + dy*dy);
    float lifeN = age / 2.0;
    float fadeIn  = smoothstep(0.0, 0.06, age);
    float fadeOut = 1.0 - smoothstep(0.7, 1.0, lifeN);
    float env = fadeIn * fadeOut;
    // v7.1: 把幅度放大 — 中心凸起更高更宽
    float bulgeW = 0.55 + age * 0.80;
    float bulge  = exp(-dist*dist / (2.0 * bulgeW * bulgeW)) * (1.0 - smoothstep(0.0, 0.55, lifeN));
    float waveR  = age * 2.10;
    float ringW  = 0.40 + age * 0.22;
    float ring   = exp(-pow((dist - waveR) / ringW, 2.0));
    // v7.1: 提升整体幅度 ×2
    float local  = (bulge * 2.4 + ring * 1.30) * env * str;
    sum += local;
    maxAmp = max(maxAmp, abs(local));
  }
  return sum;
}

void main(){
  float t = uTime * uSpeed;
  vec3 pos;
  vec2 sampleUv = safeCoverUv(aUv);
  // 切歌颜色渐变: 在新旧封面间 mix
  vec3 newCol = sampleNewCoverColor(sampleUv);
  vec3 prevCol = samplePrevCoverColor(sampleUv);
  vec3 coverColor = mix(prevCol, newCol, clamp(uColorMixT, 0.0, 1.0));
  vec4 edge = sampleEdgeColor(sampleUv);
  float depthVal = edge.r;
  float edgeVal  = edge.g;
  float fgMask   = edge.b;
  float lumVal   = edge.a;
  float maxRippleAmp = 0.0;
  float rippleZ = 0.0;

  vec3 defaultColor = mix(
    vec3(0.36, 0.28, 0.72),
    mix(vec3(0.85, 0.55, 0.95), vec3(0.45, 0.78, 0.95), aUv.x),
    aUv.y
  );
  vColor = mix(defaultColor, coverColor, uHasCover);
  vAlpha = 1.0;

  // 律动强度的真实倍数 (放大 intensity 滑块的影响)
  float K = uIntensity * 1.6;   // 滑块 1.0 → K=1.6, 滑块 1.6 → K=2.56

  // ====================================================
  //  Preset 0: SILK — 丝绸 (xy 平面, z 涟漪)
  //  v7.1: 全部位移 ×2.5
  // ====================================================
  if (uPreset < 0.5) {
    pos = position;
    rippleZ = rippleSumAt(pos.xy, maxRippleAmp);

    float midN = snoise(vec3(pos.x*1.4, pos.y*1.4, t*0.55)) * 0.6
               + snoise(vec3(pos.x*2.8+5.0, pos.y*2.8-3.0, t*0.85)) * 0.4;
    float midMask = 0.55 + 0.45 * snoise(vec3(pos.x*0.4, pos.y*0.4, t*0.18));
    float midDisp = midN * uMid * 0.55 * midMask * K;       // 0.20 → 0.55

    float trebleJ = snoise(vec3(pos.x*6.5, pos.y*6.5, t*3.5 + aRand*4.0)) * uTreble * 0.18 * K;  // 0.06→0.18
    float bassBreath = snoise(vec3(pos.x*0.35, pos.y*0.35, t*0.4)) * uBass * 0.42 * K;          // 0.14→0.42

    // AI 深度: 显著强化 (0.85 → 1.4)
    float depthZ = (depthVal - 0.5) * uAiBoost * uDepth * 1.40 * uHasDepth;

    pos.z = rippleZ * 1.30 + midDisp + trebleJ + bassBreath + depthZ;
  }

  // ====================================================
  //  Preset 1: TUNNEL — 隧道 + 自旋
  // ====================================================
  else if (uPreset < 1.5) {
    // v7.1: 整体自旋 — 整管缓慢绕 Z 轴
    float spin = t * 0.12;
    float angle = aUv.x * 2.0 * PI + spin;
    float flow = aUv.y - t * 0.08 * (1.0 + uBass * 0.55);
    flow = fract(flow);
    float zPos = (flow - 0.5) * 9.0;
    float baseR = 2.0 - uBass * 0.28 * K;                  // bass 收缩更明显
    float ripG  = sin(angle * 5.0 + zPos * 1.4 + t * 2.2) * 0.10 * (uMid + uTreble) * K;   // 0.04→0.10
    float r = baseR + ripG;
    pos.x = cos(angle) * r;
    pos.y = sin(angle) * r;
    pos.z = zPos;

    sampleUv = vec2(aUv.x, flow);
    sampleUv = safeCoverUv(sampleUv);
    newCol = sampleNewCoverColor(sampleUv);
    prevCol = samplePrevCoverColor(sampleUv);
    coverColor = mix(prevCol, newCol, clamp(uColorMixT, 0.0, 1.0));
    vColor = mix(defaultColor, coverColor, uHasCover);

    float depthFade = smoothstep(-4.5, 4.5, zPos);
    vColor *= 0.4 + depthFade * 0.7;
  }

  // ====================================================
  //  Preset 2: ORBIT — 星球 (保留自转)
  //  v7.1: 律动幅度加大
  // ====================================================
  else if (uPreset < 2.5) {
    float theta = aUv.x * 2.0 * PI;
    float phi   = (aUv.y - 0.5) * PI;
    float baseR = 2.2;
    float trebFlare = snoise(vec3(theta * 1.5, phi * 1.5, t * 0.7)) * uTreble * 0.85 * K;   // 0.40→0.85
    float bassExpand = uBass * 0.35 * K;                                                      // 0.18→0.35
    float r = baseR * (1.0 + bassExpand) + trebFlare;

    pos.x = r * cos(phi) * cos(theta);
    pos.y = r * sin(phi);
    pos.z = r * cos(phi) * sin(theta);

    float yaw = t * 0.18;
    float cy = cos(yaw), sy = sin(yaw);
    pos.xz = mat2(cy, -sy, sy, cy) * pos.xz;
  }

  // ====================================================
  //  Preset 3: VOID — 虚空 (无粒子, 适合自定义背景)
  // ====================================================
  else if (uPreset < 3.5) {
    pos = vec3((aUv.x - 0.5) * 0.01, (aUv.y - 0.5) * 0.01, -90.0);
    vAlpha = 0.0;
    vColor = vec3(0.0);
    maxRippleAmp = 0.0;
  }

  // ====================================================
  //  Preset 4: VINYL RECORD
  //  A real record layout: circular album cover in the center, black vinyl
  //  grooves outside, and a complete white particle rim.
  // ====================================================
  else if (uPreset < 4.5) {
    // 这一分支把粒子排布成唱片，中间封面、外围沟槽和边缘亮环分层处理。
    float bassDrive = smoothstep(0.08, 0.78, uBass + uBeat * 0.82);
    float highDrive = smoothstep(0.05, 0.46, uTreble);
    float hiResGuard = smoothstep(1.08, 1.55, uCoverRes);
    float edgeGuard = mix(1.0, 0.38, hiResGuard);
    float depthGuard = mix(1.0, 0.44, hiResGuard);
    float grooveGuard = mix(1.0, 0.48, hiResGuard);
    float beatGuard = mix(1.0, 0.36, hiResGuard);

    vec2 p = (aUv - 0.5) * 5.12;
    float spin = uVinylSpin;
    float cs = cos(spin), sn = sin(spin);
    vec2 rp = mat2(cs, -sn, sn, cs) * p;
    float d = length(p);
    float angle0 = atan(p.y, p.x);
    float recordR = 2.46;
    float coverR = 1.18;
    float recordAlpha = 1.0 - smoothstep(recordR - 0.02, recordR + 0.05, d);
    float coverMask = 1.0 - smoothstep(coverR - 0.012, coverR + 0.018, d);
    float border = exp(-pow((d - coverR) / 0.064, 2.0)) * edgeGuard;
    float outerRim = exp(-pow((d - (recordR - 0.050)) / 0.055, 2.0)) * edgeGuard;
    float vinylN = clamp((d - coverR) / max(0.001, recordR - coverR), 0.0, 1.0);

    pos = vec3(rp * (1.0 + bassDrive * 0.012 * beatGuard + uBeat * 0.026 * beatGuard), 0.0);
    vAlpha = recordAlpha;

    if (coverMask > 0.02) {
      vec2 coverUv = p / (coverR * 2.0) + 0.5;
      newCol = sampleNewCoverColor(coverUv);
      prevCol = samplePrevCoverColor(coverUv);
      coverColor = mix(prevCol, newCol, clamp(uColorMixT, 0.0, 1.0));
      if (hiResGuard > 0.001) {
        // 高分辨率封面下对封面颜色做轻微邻域柔化，降低密集点阵的闪烁。
        vec2 sx = vec2(0.0026, 0.0);
        vec2 sy = vec2(0.0, 0.0026);
        vec3 softNew = (sampleNewCoverColor(coverUv + sx) + sampleNewCoverColor(coverUv - sx) + sampleNewCoverColor(coverUv + sy) + sampleNewCoverColor(coverUv - sy)) * 0.25;
        vec3 softPrev = (samplePrevCoverColor(coverUv + sx) + samplePrevCoverColor(coverUv - sx) + samplePrevCoverColor(coverUv + sy) + samplePrevCoverColor(coverUv - sy)) * 0.25;
        coverColor = mix(coverColor, mix(softPrev, softNew, clamp(uColorMixT, 0.0, 1.0)), hiResGuard * 0.42);
      }
      vColor = mix(defaultColor, coverColor, uHasCover);
      float coverShade = 1.02 + 0.10 * (1.0 - smoothstep(0.0, coverR, d));
      vColor *= coverShade;
      vColor = mix(vColor, vec3(1.0), border * 0.54);
      pos.z = 0.040 + border * 0.026 * depthGuard + uBeat * 0.018 * beatGuard;
      maxRippleAmp = max(maxRippleAmp, border * 0.30 + bassDrive * 0.075 * beatGuard + uBeat * 0.075 * beatGuard);
    } else {
      // 封面圆之外使用程序化沟槽和高频刻痕模拟黑胶盘面。
      float groove = 0.5 + 0.5 * sin((d - coverR) * mix(98.0, 58.0, hiResGuard));
      float fineGroove = 0.5 + 0.5 * sin((d - coverR) * mix(170.0, 92.0, hiResGuard) + aRand * 3.0);
      float tick = smoothstep(0.82, 0.995, hash11(floor((angle0 + PI) * 38.0) + floor(d * 72.0) * 2.1));
      vec3 vinyl = vec3(0.052, 0.054, 0.058) + vec3(0.052 * grooveGuard) * groove + vec3(0.026 * grooveGuard) * fineGroove;
      vinyl = mix(vinyl, coverColor * 0.32, 0.18 * (1.0 - vinylN));
      float whiteRing = max(border * 0.92, outerRim * 0.26);
      vColor = mix(vinyl, vec3(0.92, 0.94, 0.94), whiteRing);
      vColor = mix(vColor, vec3(1.0), tick * highDrive * (0.06 + border * 0.12) * grooveGuard);
      pos.z = groove * 0.010 * grooveGuard + border * 0.024 * depthGuard + bassDrive * vinylN * 0.016 * K * beatGuard + tick * highDrive * 0.010 * grooveGuard;
      maxRippleAmp = max(maxRippleAmp, border * 0.32 + outerRim * 0.12 + bassDrive * vinylN * 0.11 * beatGuard + tick * highDrive * 0.10 * grooveGuard + uBeat * vinylN * 0.08 * beatGuard);
    }
  }

  // ====================================================
  //  Preset 5: WALLPAPER PULSE
  //  Layered music-particle wallpaper: aurora ribbons, depth sparks,
  //  and cover-colored audio flow.
  // ====================================================
  else {
    // 壁纸预设把大多数粒子分配给丝带层，少量粒子分配给远景尘点层。
    float bassGlow = smoothstep(0.07, 0.78, uBass) * 0.34 + uBeat * 0.014;
    float midGlow = smoothstep(0.07, 0.62, uMid) * 0.42;
    float highGlow = smoothstep(0.04, 0.46, uTreble) * 0.46;
    float lane = aUv.y;
    float transition = clamp(uBurstAmt, 0.0, 1.0);

    if (lane < 0.80) {
      // 前 80% 粒子生成横向流动的极光丝带。
      float laneWarp = snoise(vec3(aUv.x * 0.42, lane * 1.7, t * 0.026)) * 0.11 + (hash11(aRand * 73.1) - 0.5) * 0.045;
      float warpedLane = clamp(lane + laneWarp, 0.0, 0.80);
      float bandCoord = warpedLane / 0.80 * 5.65 + snoise(vec3(aUv.x * 0.82, lane * 2.25, t * 0.032)) * 0.62;
      float band = floor(bandCoord);
      float local = fract(bandCoord + hash11(band * 9.13 + aRand * 2.4) * 0.18);
      float bandN = clamp((band + 0.5) / 5.65, 0.0, 1.0);
      float seed = hash11(band * 19.17 + aRand * 31.0);
      float flow = fract(aUv.x + t * (0.0034 + bandN * 0.0038 + seed * 0.0022) + seed * 0.53);
      float arc = (flow - 0.5) * PI * (1.35 + bandN * 0.72 + seed * 0.24);
      float armCurve = sin(arc + bandN * 2.2 + seed * 5.3);
      float spiralRadius = 9.2 + bandN * 11.8 + seed * 6.0 + local * 2.9;
      float x = cos(arc * 0.72 + bandN * 0.92 + seed * 1.3) * spiralRadius + (flow - 0.5) * (13.5 + bandN * 9.5);
      float ribbonPhase = flow * PI * 2.0 * (0.55 + bandN * 0.24 + seed * 0.10) + t * (0.010 + bandN * 0.007) + seed * 5.7;
      float broadWave = sin(ribbonPhase) * 0.92;
      float fineWave = sin(ribbonPhase * (1.36 + seed * 0.62) - t * 0.044 + seed * 5.0) * 0.045;
      float yBase = (bandN - 0.5) * 13.2 + armCurve * (2.3 + bandN * 1.6) + (seed - 0.5) * 1.85 + snoise(vec3(bandN * 2.0, flow * 0.62, seed)) * 0.92;
      float ridgeCenter = 0.43 + (seed - 0.5) * 0.18;
      float ridge = exp(-pow((local - ridgeCenter) / (0.25 + seed * 0.04), 2.0));
      float softMask = smoothstep(0.010, 0.12, lane) * (1.0 - smoothstep(0.72, 0.81, lane));
      float ribbonNoise = snoise(vec3(flow * 1.18 + seed, bandN * 2.0, t * 0.018)) * 0.74;
      float zLayer = mix(-23.5, 15.5, bandN) + (seed - 0.5) * 6.0;

      pos.x = x + ribbonNoise * 1.40 + sin(t * 0.012 + seed * 8.0) * 0.22;
      pos.y = yBase + broadWave + fineWave + (local - 0.5) * (0.58 + ridge * 0.14);
      pos.z = zLayer + broadWave * 1.35 + ribbonNoise * 1.85;

      float pulseLine = 0.5 + 0.5 * sin(ribbonPhase * (1.7 + seed * 0.9) - t * 0.32 + seed * 6.0);
      vec3 aurora = mix(vec3(0.52, 0.86, 1.0), vec3(0.70, 0.58, 1.0), bandN);
      aurora = mix(aurora, vec3(0.96, 0.98, 0.92), bassGlow * 0.05);
      vAlpha = (0.18 + ridge * 0.78 + pulseLine * highGlow * 0.035 + bassGlow * 0.025) * softMask * (0.96 + transition * 0.02);
      vColor = mix(coverColor, aurora, 0.62 + ridge * 0.22) * (0.76 + ridge * 0.86 + pulseLine * highGlow * 0.05 + bassGlow * 0.04);
      maxRippleAmp = max(maxRippleAmp, ridge * (0.12 + midGlow * 0.05) + pulseLine * highGlow * 0.045 + bassGlow * 0.030);
    } else {
      // 剩余粒子作为远景尘点和星光，提供空间层次。
      float q = (lane - 0.80) / 0.20;
      float seed = hash11(aRand * 917.0 + floor(q * 130.0));
      float depth = mix(-32.0, 18.0, seed);
      float drift = fract(aUv.x + t * (0.0014 + seed * 0.0048) + seed * 0.63);
      float cluster = snoise(vec3(seed * 2.0, q * 3.2, t * 0.007));
      float x = (drift - 0.5) * (45.0 + seed * 22.0) + cluster * 3.4;
      float y = (hash11(aRand * 331.0 + seed * 5.0) - 0.5) * 22.0 + sin(t * (0.018 + seed * 0.028) + seed * 7.0) * 0.86;
      float z = depth + sin(t * (0.020 + seed * 0.032) + aRand * 8.0) * 1.05;
      float twinkle = pow(0.5 + 0.5 * sin(t * (0.24 + seed * 0.42) + aRand * 17.0), 5.0);
      float dust = smoothstep(0.22, 0.98, hash11(aRand * 661.0 + floor(q * 160.0)));

      pos = vec3(x, y, z);
      vAlpha = dust * (0.16 + twinkle * 0.46 + highGlow * 0.025 + bassGlow * 0.018) * (1.0 - q * 0.06);
      vColor = mix(coverColor, vec3(0.92, 0.97, 1.0), 0.62 + twinkle * 0.14) * (0.72 + twinkle * 0.62 + bassGlow * 0.025);
      maxRippleAmp = max(maxRippleAmp, twinkle * highGlow * 0.055 + dust * bassGlow * 0.030);
    }

    if (transition > 0.001) {
      // 预设切换时用轻微爆发扰动掩盖粒子重新组织。
      float bloom = smoothstep(0.0, 1.0, transition);
      vec2 burstVec = pos.xy + vec2(hash11(aRand * 31.0) - 0.5, hash11(aRand * 47.0) - 0.5) * 0.75;
      vec2 burstDir = burstVec / max(length(burstVec), 0.001);
      pos.xy += burstDir * bloom * 0.026;
      pos.xy += vec2(snoise(vec3(aRand, t * 0.014, 1.0)), snoise(vec3(aRand, t * 0.014, 5.0))) * bloom * 0.06;
      pos.xy *= 1.0 + bloom * 0.014;
      pos.z += (hash11(aRand * 123.0) - 0.5) * bloom * 0.18;
      vAlpha *= 0.86 + bloom * 0.22;
      maxRippleAmp = max(maxRippleAmp, bloom * 0.10);
    }
  }

  // ====================================================
  //  鼠标交互 (仅 SILK)
  // ====================================================
  if (uMouseActive > 0.5 && uPreset < 0.5) {
    float mdx = pos.x - uMouseXY.x;
    float mdy = pos.y - uMouseXY.y;
    float md = sqrt(mdx*mdx + mdy*mdy);
    if (md < 1.0) {
      float push = (1.0 - md) * (1.0 - md);
      pos.z += push * 0.55;
    }
  }

  // ====================================================
  //  通用: 离散感 / 扭曲
  // ====================================================
  if (uScatter > 0.001) {
    vec2 jdir = vec2(cos(aRand * 6.2831), sin(aRand * 6.2831));
    pos.xy += jdir * uScatter * (0.05 + uTreble * 0.10);
  }
  if (uTwist > 0.001 && uPreset < 0.5) {
    float ta = uTwist * pos.z * 0.6;
    float cs = cos(ta), sn = sin(ta);
    pos.xy = mat2(cs, -sn, sn, cs) * pos.xy;
  }

  // 颜色
  float vinylHiResGuard = smoothstep(1.08, 1.55, uCoverRes) * step(3.5, uPreset) * (1.0 - step(4.5, uPreset));
  float edgeBoost = uEdgeEnabled * edgeVal * mix(1.0, 0.42, vinylHiResGuard);
  vSourceLum = dot(max(vColor, vec3(0.0)), vec3(0.299, 0.587, 0.114));
  float blackParticleGuard = 1.0 - smoothstep(0.025, 0.115, vSourceLum);
  vEdgeBoost = edgeBoost * (uPreset > 3.5 ? 0.22 : 1.0) * (1.0 - blackParticleGuard);
  vColor = pow(max(vColor, vec3(0.0)), vec3(1.0 / max(0.35, uColorBoost)));
  float edgeColorMix = edgeBoost * (uPreset > 3.5 ? 0.20 : 0.50) * (1.0 - blackParticleGuard);
  vColor = mix(vColor, vColor + vec3(0.20), edgeColorMix);
  float tintLum = max(max(vColor.r, vColor.g), vColor.b);
  vec3 tintedColor = uTintColor * max(0.24, tintLum * 1.12);
  vColor = mix(vColor, tintedColor, clamp(uTintStrength, 0.0, 1.0) * (1.0 - blackParticleGuard));

  vBright = 0.82 + maxRippleAmp * 0.55 + uBass * 0.10 + edgeBoost * 0.30 + uEnergy * 0.05 + uBurstAmt * 0.40;
  if (uPreset > 4.5) {
    vBright = 0.94 + maxRippleAmp * 0.34 + uBass * 0.020 + uEnergy * 0.026 + uBurstAmt * 0.025;
  } else if (uPreset > 3.5) {
    vBright = 0.94 + maxRippleAmp * 0.64 + uBass * 0.08 + edgeBoost * 0.12 + uEnergy * 0.05 + uBeat * 0.16 + uBurstAmt * 0.16;
  }
  vRipple = clamp(maxRippleAmp * 1.5, 0.0, 1.0);

  if (uHasDepth > 0.5 && uPreset < 0.5) {
    float bgMul = mix(1.0, 0.55, uBgFade * (1.0 - fgMask));
    vBright *= bgMul;
  }
  float loadingMistSize = 1.0;

  // 加载形态: 雾状微尘流，避免廉价旋转圆环
  if (uLoading > 0.001) {
    float mistSeed = hash11(aRand * 931.7);
    float mistLayer = floor(mistSeed * 4.0);
    float layerN = (mistLayer + 0.5) / 4.0;
    float mistAngle = aRand * 6.2831 + uTime * (0.16 + mistSeed * 0.18) + snoise(vec3(aRand * 2.1, uTime * 0.24, 2.0)) * 1.85;
    float mistR = mix(1.35, 3.15, sqrt(hash11(aRand * 127.3))) * (1.0 + sin(uTime * 0.42 + aRand * 7.0) * 0.13);
    vec2 mistCurl = vec2(
      snoise(vec3(aRand * 4.1, uTime * 0.32, 3.0)),
      snoise(vec3(aRand * 4.7, uTime * 0.30, 8.0))
    );
    float mistBreath = 0.5 + 0.5 * sin(uTime * (0.82 + mistSeed * 0.55) + aRand * 17.0);
    float mistRibbon = sin(mistAngle * (1.35 + layerN * 0.55) + uTime * 0.34 + mistSeed * 4.0);
    float glowPick = smoothstep(0.88, 0.997, hash11(aRand * 1501.0 + mistLayer * 17.0));
    float dustPick = 0.34 + glowPick * 0.66;
    vec3 mistPos = vec3(
      cos(mistAngle) * mistR * (1.24 + mistCurl.x * 0.16) + mistCurl.x * 0.72,
      sin(mistAngle * 0.82 + mistRibbon * 0.25) * mistR * (0.56 + layerN * 0.10) + mistCurl.y * 0.62,
      (layerN - 0.5) * 4.85 + mistCurl.x * 0.56 + mistBreath * 0.36 + mistRibbon * 0.24
    );
    vec3 mistCol = mix(vec3(0.62, 0.86, 0.84), vec3(0.36, 0.46, 0.78), mistSeed);
    mistCol = mix(mistCol, vec3(0.94, 1.0, 0.97), glowPick * (0.45 + mistBreath * 0.35));
    vColor = mix(vColor, mistCol, uLoading * 0.78);
    vBright = mix(vBright, 0.20 + mistBreath * 0.18 + abs(mistCurl.x) * 0.06 + glowPick * (0.72 + abs(mistRibbon) * 0.24), uLoading);
    vAlpha = mix(vAlpha, 0.08 + mistBreath * 0.11 + dustPick * 0.11 + glowPick * 0.30, uLoading);
    pos = mix(pos, mistPos, uLoading);
    loadingMistSize = 1.26 + mistBreath * 0.24 + abs(mistRibbon) * 0.14 + glowPick * 0.78;
  }

  vec4 mvPos = modelViewMatrix * vec4(pos, 1.0);
  float depthSize = 36.0 / max(0.5, -mvPos.z);
  float audioBoost = 1.0 + maxRippleAmp * 0.7 + edgeBoost * 0.55 + uBeat * 0.30 + uBurstAmt * 0.5;
  float sz = clamp(depthSize * audioBoost, 1.05, 4.95);
  if (uPreset > 4.5) {
    float flowDrive = uBass * 0.070 + uMid * 0.046 + uTreble * 0.060 + uBurstAmt * 0.090 + uBeat * 0.055;
    sz = clamp(depthSize * (1.05 + flowDrive), 1.00, 5.45);
  } else if (uPreset > 3.5) {
    float ringDrive = uBass * 0.30 + uMid * 0.18 + uTreble * 0.22 + uBeat * 0.30;
    sz = clamp(depthSize * (0.90 + ringDrive * 0.62), 1.05, 3.90);
  }
  // 加载态下粒子稍大
  sz = mix(sz, sz * loadingMistSize, uLoading);
  gl_PointSize = sz * uPixel * uPointScale;
  gl_Position = projectionMatrix * mvPos;
}
`;

// ----- 片元 Shader -----
var fs = `
precision highp float;
uniform sampler2D uDotTex;
uniform float uAlpha, uPreset, uParticleDim;
varying vec3 vColor;
varying float vBright, vRipple, vEdgeBoost, vAlpha, vSourceLum;

void main(){
  vec4 tex = texture2D(uDotTex, gl_PointCoord);
  if (tex.a < 0.02) discard;
  vec3 col = vColor * vBright;
  col = mix(col, col * 1.3 + vec3(0.05), vEdgeBoost * 0.35);
  col = mix(col, col * 1.2, vRipple * 0.4);
  float keepBlack = 1.0 - smoothstep(0.025, 0.115, vSourceLum);
  float nonBlack = 1.0 - keepBlack;
  float dotDist = length(gl_PointCoord - vec2(0.5)) * 2.0;
  float readableRim = smoothstep(0.44, 0.94, dotDist) * (1.0 - smoothstep(0.94, 1.08, dotDist)) * tex.a;
  float outLum = dot(col, vec3(0.299, 0.587, 0.114));
  float lightParticle = smoothstep(0.50, 0.82, outLum) * nonBlack;
  float darkParticle = (1.0 - smoothstep(0.20, 0.50, outLum)) * nonBlack;
  col = mix(col, vec3(0.0), readableRim * lightParticle * 0.38);
  col = mix(col, vec3(1.0), readableRim * darkParticle * 0.20);
  col = clamp(col, vec3(0.0), vec3(1.6));
  gl_FragColor = vec4(col, tex.a * uAlpha * uParticleDim * vAlpha);
}
`;

var material = new THREE.ShaderMaterial({
  // 主材质负责可读的正常混合粒子层。
  uniforms: uniforms, vertexShader: vs, fragmentShader: fs,
  transparent: true, depthWrite: false, blending: THREE.NormalBlending,
});

// 辉光顶点 shader 复用主顶点逻辑，只额外加入 uBloomSize 放大点尺寸。
var bloomVs = vs
  .replace('uniform float uMouseActive, uPixel, uColorMixT, uLoading;', 'uniform float uMouseActive, uPixel, uColorMixT, uLoading, uBloomSize;')
  .replace('gl_PointSize = sz * uPixel * uPointScale;', 'gl_PointSize = sz * uPixel * uPointScale * uBloomSize;');
// 辉光片元 shader 使用加法混合，给亮点和边缘提供柔光。
var bloomFs = `
precision highp float;
uniform sampler2D uDotTex;
uniform float uAlpha, uBloomStrength, uPreset, uParticleDim;
varying vec3 vColor;
varying float vBright, vRipple, vEdgeBoost, vAlpha, vSourceLum;

void main(){
  vec4 tex = texture2D(uDotTex, gl_PointCoord);
  if (tex.a < 0.01) discard;
  float soft = tex.a * tex.a;
  vec3 col = vColor * (0.55 + vBright * 0.62);
  col = mix(col, col + vec3(0.22, 0.18, 0.10), vEdgeBoost * 0.35);
  col = clamp(col, vec3(0.0), vec3(1.8));
  float pulse = 1.0 + vRipple * 0.65;
  float keepBlack = 1.0 - smoothstep(0.025, 0.115, vSourceLum);
  float bloomKeep = 1.0 - keepBlack * 0.92;
  gl_FragColor = vec4(col, soft * uAlpha * uBloomStrength * uParticleDim * pulse * 0.55 * vAlpha * bloomKeep);
}
`;
var bloomMaterial = new THREE.ShaderMaterial({
  // 辉光材质关闭深度测试，让柔光不被主粒子层遮断。
  uniforms: uniforms, vertexShader: bloomVs, fragmentShader: bloomFs,
  transparent: true, depthWrite: false, depthTest: false, blending: THREE.AdditiveBlending,
});
// 辉光粒子层先渲染，作为主粒子背后的柔光底。
var bloomParticles = new THREE.Points(geo, bloomMaterial);
bloomParticles.frustumCulled = false;
bloomParticles.renderOrder = 0;
scene.add(bloomParticles);
// 主粒子层负责最终可见的封面颜色、形状和可读边缘。
var particles = new THREE.Points(geo, material);
particles.frustumCulled = false;
particles.renderOrder = 1;
scene.add(particles);
// 调试日志保留原样，用于确认主粒子 shell 已经完成初始化。
console.log('v7 shell loaded, JS pending');

// ============================================================
//  浮空粒子层 (独立 Points)
//   v7.1: 速度大幅放慢, 改用 sin/cos 长周期漂移 (优雅而非乱飞)
// ============================================================
// 浮空粒子数量，当前实现保留参数但默认禁用这一层。
var FLOAT_COUNT = 1300;
// 浮空粒子的 Points 容器；为 null 表示未创建或已销毁。
var floatGroup = null;
// 浮空粒子几何数据缓存：当前位置、基准位置、相位和颜色。
var floatPositionsArr = null, floatBaseArr = null, floatPhaseArr = null, floatColorArr = null;

// 创建浮空粒子层；当前函数开头会主动禁用并返回，后续代码作为保留实现存在。
function createFloatLayer() {
  // 强制关闭浮空层配置，避免这一层参与当前视觉。
  fx.floatLayer = false;
  // 同步把 shader 透明度归零。
  uniforms.uFloatAlpha.value = 0;
  // 如果历史上已创建过浮空层，立即销毁。
  if (floatGroup) destroyFloatLayer();
  // 当前版本不继续创建浮空层，下方实现保留以便后续恢复。
  return;
  if (floatGroup) return;
  // 浮空层使用独立几何，避免和封面粒子共享属性。
  var fgeo = new THREE.BufferGeometry();
  // 当前位置数组。
  floatPositionsArr = new Float32Array(FLOAT_COUNT * 3);
  // 基准位置数组，shader 漂移围绕这个位置展开。
  floatBaseArr      = new Float32Array(FLOAT_COUNT * 3);  // 基准位置
  // 每个粒子的三轴相位，控制漂移节奏差异。
  floatPhaseArr     = new Float32Array(FLOAT_COUNT * 3);  // 每粒子相位 (0..2π)
  // 每个粒子的 RGB 颜色。
  floatColorArr     = new Float32Array(FLOAT_COUNT * 3);
  // 每个粒子的随机种子。
  var floatRandArr  = new Float32Array(FLOAT_COUNT);
  // 每个粒子的漂移幅度。
  var floatAmpArr   = new Float32Array(FLOAT_COUNT);      // 漂移幅度 (0.15-0.45)
  for (var i = 0; i < FLOAT_COUNT; i++) {
    // 大部分粒子围绕中心形成光晕，少量粒子散布在更大的空间里。
    var halo = i < FLOAT_COUNT * 0.76;
    // 单个粒子的基准坐标。
    var bx, by, bz;
    if (halo) {
      // 光晕粒子用极坐标分布，形成椭圆环绕效果。
      var a = Math.random() * Math.PI * 2;
      var r = 0.62 + Math.pow(Math.random(), 0.72) * 2.75;
      var lane = (Math.random() - 0.5) * 0.62;
      bx = Math.cos(a) * r;
      by = Math.sin(a) * r * 0.54 + lane;
      bz = (Math.random() - 0.5) * 2.4 - 0.25;
    } else {
      // 非光晕粒子随机填充更大的背景空间。
      bx = (Math.random() - 0.5) * 8.4;
      by = (Math.random() - 0.5) * 5.8;
      bz = (Math.random() - 0.5) * 5.6;
    }
    // 写入基准位置和初始位置。
    floatBaseArr[i*3]   = bx; floatBaseArr[i*3+1] = by; floatBaseArr[i*3+2] = bz;
    floatPositionsArr[i*3]   = bx;
    floatPositionsArr[i*3+1] = by;
    floatPositionsArr[i*3+2] = bz;
    floatPhaseArr[i*3]   = Math.random() * Math.PI * 2;
    floatPhaseArr[i*3+1] = Math.random() * Math.PI * 2;
    floatPhaseArr[i*3+2] = Math.random() * Math.PI * 2;
    floatAmpArr[i] = 0.15 + Math.random() * 0.35;
    // 初始颜色使用接近白色的细微随机值，封面加载后会被替换。
    var white = 0.88 + Math.random() * 0.12;
    floatColorArr[i*3]   = white;
    floatColorArr[i*3+1] = white;
    floatColorArr[i*3+2] = white;
    floatRandArr[i] = Math.random();
  }
  fgeo.setAttribute('position', new THREE.BufferAttribute(floatPositionsArr, 3));
  fgeo.setAttribute('aColor',   new THREE.BufferAttribute(floatColorArr, 3));
  fgeo.setAttribute('aRand',    new THREE.BufferAttribute(floatRandArr, 1));

  // 把 amp + phase 存到 attribute 让 shader 端做漂移 (避免 JS 每帧改 buffer)
  fgeo.setAttribute('aAmp',     new THREE.BufferAttribute(floatAmpArr, 1));
  fgeo.setAttribute('aPhase',   new THREE.BufferAttribute(floatPhaseArr, 3));

  // 浮空层顶点 shader 负责慢速旋转、呼吸和三轴漂移。
  var fvs = `
    precision highp float;
    uniform float uTime, uBass, uPixel, uFloatAlpha;
    attribute vec3 aColor;
    attribute vec3 aPhase;
    attribute float aRand, aAmp;
    varying vec3 vC;
    varying float vA;
    void main(){
      vec3 pos = position;
      float orbit = uTime * (0.030 + aRand * 0.034);
      float cs = cos(orbit), sn = sin(orbit);
      pos.xy = mat2(cs, -sn, sn, cs) * pos.xy;
      float breathe = 1.0 + sin(uTime * 0.34 + aPhase.x) * 0.045;
      pos.xy *= breathe;
      pos.x += sin(uTime * (0.18 + aRand * 0.05) + aPhase.x) * aAmp * 0.34;
      pos.y += cos(uTime * (0.15 + aRand * 0.06) + aPhase.y) * aAmp * 0.30;
      pos.z += sin(uTime * (0.11 + aRand * 0.04) + aPhase.z) * aAmp * 0.68 + uBass * 0.10 * sin(aRand * 12.0);
      vC = aColor;
      vec4 mvPos = modelViewMatrix * vec4(pos, 1.0);
      float dist = -mvPos.z;
      float twinkle = 0.62 + 0.38 * sin(uTime * (0.42 + aRand * 0.34) + aPhase.z);
      vA = clamp(0.22 + (5.0 - dist) * 0.10, 0.055, 0.58) * twinkle;
      float sz = clamp(40.0 / max(0.5, dist), 1.3, 4.1);
      gl_PointSize = sz * uPixel;
      gl_Position = projectionMatrix * mvPos;
    }
  `;
  // 浮空层片元 shader 只使用圆点纹理控制透明边缘。
  var ffs = `
    precision highp float;
    uniform sampler2D uDotTex;
    uniform float uFloatAlpha;
    varying vec3 vC;
    varying float vA;
    void main(){
      vec4 tex = texture2D(uDotTex, gl_PointCoord);
      if (tex.a < 0.02) discard;
      gl_FragColor = vec4(vC, tex.a * vA * uFloatAlpha);
    }
  `;
  // 浮空层材质复用全局时间、低频、像素比和圆点纹理 uniform。
  var fmat = new THREE.ShaderMaterial({
    uniforms: {
      uTime: uniforms.uTime,
      uBass: uniforms.uBass,
      uPixel: uniforms.uPixel,
      uDotTex: uniforms.uDotTex,
      uFloatAlpha: uniforms.uFloatAlpha,
    },
    vertexShader: fvs, fragmentShader: ffs,
    transparent:true, depthWrite:false, blending: THREE.AdditiveBlending,
  });
  // 创建浮空 Points 并加入主场景。
  floatGroup = new THREE.Points(fgeo, fmat);
  floatGroup.frustumCulled = false;
  scene.add(floatGroup);
}
// 销毁浮空粒子层并释放对应 GPU 资源。
function destroyFloatLayer() {
  // 未创建时无需处理。
  if (!floatGroup) return;
  scene.remove(floatGroup);
  // 几何和材质都由浮空层独占，可以直接释放。
  floatGroup.geometry.dispose(); floatGroup.material.dispose();
  floatGroup = null;
}

// ============================================================
//  安魂 — 3D 粒子建模层
// ============================================================
// 骷髅粒子预设在 fx.preset 中的索引。
var SKULL_PRESET_INDEX = 6;
// 骷髅模型的基础 X 轴俯仰角。
var SKULL_MODEL_BASE_ROTATION_X = -0.26;
// 骷髅模型的基础 Y 轴朝向角。
var SKULL_MODEL_BASE_ROTATION_Y = 0.00;
// 骷髅模型的默认缩放。
var SKULL_MODEL_SCALE = 2.34;
// 骷髅模型默认摆放位置。
var SKULL_MODEL_BASE_POSITION = { x: 0, y: 0.22, z: 0.10 };
// 音频驱动的整体脉冲缩放缓存。
var skullAmpPulse = 0;
// 节拍闪光强度缓存。
var skullBeatFlash = 0;
// 下颌张开程度缓存。
var skullJawOpen = 0;
// 骷髅专属相机接管混合度。
var skullCameraBlend = 0;
// 当前滚轮缩放值。
var skullWheelZoom = 0;
// 滚轮缩放目标值，逐帧缓动到 skullWheelZoom。
var skullWheelZoomTarget = 0;
// 骷髅相机目标位置。
var skullCameraTargetPos = new THREE.Vector3();
// 骷髅相机目标注视点。
var skullCameraTargetLook = new THREE.Vector3();
// 骷髅普通布局下的相机位置。
var skullCameraBasePos = new THREE.Vector3();
// 骷髅普通布局下的相机注视点。
var skullCameraBaseLook = new THREE.Vector3();
// 歌单架组合布局下的相机位置。
var skullCameraShelfPos = new THREE.Vector3();
// 歌单架组合布局下的相机注视点。
var skullCameraShelfLook = new THREE.Vector3();
// 与轨道相机注视点混合后的实际 lookAt。
var skullCameraMixedLook = new THREE.Vector3();
// 歌单架组合构图混合度。
var skullShelfCameraMix = 0;
// 歌词贴近骷髅嘴部时使用的本地坐标。
var skullLyricMouthLocal = new THREE.Vector3(0.025, -0.72, 0.62);
// 骷髅嘴部在世界坐标中的歌词目标点。
var skullLyricMouthTarget = new THREE.Vector3();
// 骷髅嘴部朝向向量。
var skullLyricMouthForward = new THREE.Vector3();
// 骷髅嘴部朝向四元数。
var skullLyricMouthQuat = new THREE.Quaternion();
// 让嘴部歌词保持可读性的修正四元数。
var skullLyricReadableQuat = new THREE.Quaternion();
// 骷髅粒子的 Points 容器。
var skullParticleGroup = null;
// 骷髅粒子整体透明度缓动值。
var skullParticleOpacity = 0;
// 骷髅粒子二进制资源缓存，避免重复 fetch。
var skullParticleAsset = { data: null, promise: null, failed: false };
// 骷髅默认色板和中性色板。
var skullBaseColors = {
  boneA: new THREE.Color('#b8ae98'),
  boneB: new THREE.Color('#fff4d8'),
  shadow: new THREE.Color('#100d0d'),
  light: new THREE.Color('#ffe3a0'),
  neutralBoneA: new THREE.Color('#9fb7c8'),
  neutralBoneB: new THREE.Color('#eef9ff'),
  neutralShadow: new THREE.Color('#070b12'),
  neutralLight: new THREE.Color('#d6f3ff')
};
// 骷髅调色时复用的 Color 对象，减少每帧分配。
var skullTintScratch = {
  tint: new THREE.Color(),
  soft: new THREE.Color(),
  bright: new THREE.Color(),
  dark: new THREE.Color(),
  boneA: new THREE.Color(),
  boneB: new THREE.Color(),
  shadow: new THREE.Color(),
  light: new THREE.Color()
};

// 计算骷髅预设当前应该使用的色调和强度。
function effectiveSkullVisualTint() {
  // 优先读取舞台歌词从封面提取出的色板。
  var pal = stageLyrics && (stageLyrics.coverPalette || stageLyrics.palette) || {};
  // 自定义色调模式使用用户设置，否则跟随封面色板。
  var custom = fx && fx.visualTintMode === 'custom';
  // 色彩优先级：自定义色、封面辅助色、封面主色、默认色。
  var color = custom
    ? fx.visualTintColor
    : (pal.secondary || pal.primary || fx.visualTintColor || fxDefaults.visualTintColor || '#9db8cf');
  // 统一成合法十六进制颜色，防止无效设置写入 Three.Color。
  color = normalizeHexColor(color || '#9db8cf', '#9db8cf');
  // 自定义色调更强，封面色板只轻度影响骨色。
  var strength = custom ? 0.98 : (pal && (pal.secondary || pal.primary) ? 0.30 : 0.14);
  return { color: color, strength: strength, custom: custom };
}

// 把当前视觉色调同步到骷髅粒子材质。
function syncSkullParticleColors() {
  // 骷髅层还未创建时无需同步。
  if (!skullParticleGroup || !skullParticleGroup.material || !skullParticleGroup.material.uniforms) return;
  // 缓存 uniform 引用，减少重复链式访问。
  var u = skullParticleGroup.material.uniforms;
  // 取得当前有效色调。
  var tint = effectiveSkullVisualTint();
  // 自定义模式会使用更高的色彩替换权重。
  var custom = !!tint.custom;
  // 限制强度范围，避免骨色被完全冲掉。
  var strength = clampRange(Number(tint.strength) || 0, 0, custom ? 0.99 : 0.78);
  // 先把字符串色写入 scratch，再派生柔和、高亮和阴影色。
  skullTintScratch.tint.set(tint.color);
  skullTintScratch.soft.copy(skullTintScratch.tint).lerp(new THREE.Color('#e8f5ff'), custom ? 0.05 : 0.28);
  skullTintScratch.bright.copy(skullTintScratch.tint).lerp(new THREE.Color(custom ? '#f6fbff' : '#fff7d6'), custom ? 0.14 : 0.46);
  skullTintScratch.dark.copy(skullTintScratch.tint).lerp(new THREE.Color('#05070c'), custom ? 0.74 : 0.72);
  skullTintScratch.boneA.copy(custom ? skullBaseColors.neutralBoneA : skullBaseColors.boneA).lerp(skullTintScratch.soft, strength * (custom ? 0.99 : 0.64));
  skullTintScratch.boneB.copy(custom ? skullBaseColors.neutralBoneB : skullBaseColors.boneB).lerp(skullTintScratch.bright, strength * (custom ? 0.94 : 0.46));
  skullTintScratch.shadow.copy(custom ? skullBaseColors.neutralShadow : skullBaseColors.shadow).lerp(skullTintScratch.dark, strength * (custom ? 0.72 : 0.42));
  skullTintScratch.light.copy(custom ? skullBaseColors.neutralLight : skullBaseColors.light).lerp(skullTintScratch.bright, strength * (custom ? 0.98 : 0.76));
  if (u.uColorA) u.uColorA.value.copy(skullTintScratch.boneA);
  if (u.uColorB) u.uColorB.value.copy(skullTintScratch.boneB);
  if (u.uShadow) u.uShadow.value.copy(skullTintScratch.shadow);
  if (u.uLight) u.uLight.value.copy(skullTintScratch.light);
}

// 根据二进制点数据构建骷髅 BufferGeometry。
function buildSkullParticleGeometryFromAsset(points) {
  // 资源每五个 float 描述一个点：x、y、z、kind、seed。
  var count = Math.floor((points && points.length || 0) / 5);
  // 骷髅粒子几何只包含位置、随机种子和部位类型。
  var geo = new THREE.BufferGeometry();
  // 位置数组。
  var positions = new Float32Array(count * 3);
  // 随机种子数组。
  var seeds = new Float32Array(count);
  // 部位类型数组，用于 shader 区分骨面、下颌和细节。
  var kinds = new Float32Array(count);
  for (var i = 0; i < count; i++) {
    positions[i * 3] = points[i * 5];
    positions[i * 3 + 1] = points[i * 5 + 1];
    positions[i * 3 + 2] = points[i * 5 + 2];
    kinds[i] = points[i * 5 + 3];
    seeds[i] = points[i * 5 + 4];
  }
  geo.setAttribute('position', new THREE.BufferAttribute(positions, 3));
  geo.setAttribute('seed', new THREE.BufferAttribute(seeds, 1));
  geo.setAttribute('kind', new THREE.BufferAttribute(kinds, 1));
  return geo;
}

// 异步加载骷髅粒子二进制资源，并缓存成功或失败状态。
function loadSkullParticleAsset() {
  // 已有数据、正在加载或已失败时复用当前状态，不重复发起请求。
  if (skullParticleAsset.data || skullParticleAsset.promise || skullParticleAsset.failed) return skullParticleAsset.promise || Promise.resolve(skullParticleAsset.data);
  if (typeof fetch !== 'function') {
    // 没有 fetch 的环境无法加载外部二进制资源，标记失败后静默返回。
    skullParticleAsset.failed = true;
    return Promise.resolve(null);
  }
  // 使用 reload 缓存策略确保开发期间能拿到新版点云资源。
  skullParticleAsset.promise = fetch('assets/skull-decimation-points.bin?v=regular-surface-teeth-soften-20260621', { cache: 'reload' })
    .then(function(res){
      // HTTP 状态异常时进入 catch，后续不会反复重试。
      if (!res.ok) throw new Error('skull asset ' + res.status);
      return res.arrayBuffer();
    })
    .then(function(buf){
      // 每个点占 20 字节，长度不匹配说明资源格式错误。
      if (!buf || buf.byteLength < 20 || buf.byteLength % 20 !== 0) throw new Error('invalid skull asset');
      skullParticleAsset.data = new Float32Array(buf);
      skullParticleAsset.promise = null;
      return skullParticleAsset.data;
    })
    .catch(function(err){
      // 资源加载失败只降级为不可用，不阻断主播放器。
      console.warn('skull particle asset load failed:', err);
      skullParticleAsset.failed = true;
      skullParticleAsset.promise = null;
      return null;
    });
  return skullParticleAsset.promise;
}

// 向备用骷髅点数组追加一个点。
function skullPushPoint(pos, seed, kind, x, y, z, k) {
  pos.push(x, y, z);
  // 备用点云使用随机种子驱动 shader 闪烁和微扰。
  seed.push(Math.random() * 1000);
  // kind 缺省为 0，代表普通骨面。
  kind.push(k == null ? 0 : k);
}
// 按参数曲线生成一串备用骷髅点。
function skullPushCurve(pos, seed, kind, count, fn, k, jitter) {
  // jitter 用于打散过于规则的曲线点。
  jitter = jitter == null ? 0.012 : jitter;
  for (var i = 0; i < count; i++) {
    // t 是曲线归一化位置。
    var t = count > 1 ? i / (count - 1) : 0;
    // fn 返回曲线上当前点的三维坐标。
    var p = fn(t);
    skullPushPoint(pos, seed, kind, p.x + (Math.random() - 0.5) * jitter, p.y + (Math.random() - 0.5) * jitter, p.z + (Math.random() - 0.5) * jitter, k);
  }
}
// 创建骷髅粒子层，优先使用外部点云资源，备用代码保留程序化点云生成逻辑。
function createSkullParticleLayer() {
  // 已创建时直接复用。
  if (skullParticleGroup) return skullParticleGroup;
  // 当前主路径要求资源先加载成功。
  var asset = skullParticleAsset.data;
  if (!asset) return null;
  // 备用程序化点云数组；正常资源路径下不会填充。
  var pos = [];
  var seed = [];
  var kind = [];
  if (!asset) {

  // 备用点云中的二维旋转辅助函数。
  function rotate2(x, y, a) {
    var c = Math.cos(a), s = Math.sin(a);
    return { x:x * c - y * s, y:x * s + y * c };
  }
  // 判断备用点是否落入眼眶挖空区域。
  function eyeCut(x, y, z, side) {
    if (z < 0.16) return false;
    var p = rotate2(x - side * 0.38, y - 0.02, side * 0.10);
    var almond = Math.pow(Math.abs(p.x) / 0.34, 1.70) + Math.pow(Math.abs(p.y) / 0.215, 1.34);
    var slantGate = p.y < 0.22 - Math.abs(p.x) * 0.12 && p.y > -0.24 + Math.abs(p.x) * 0.10;
    return almond < 1.0 && slantGate;
  }
  // 判断备用点是否落入鼻孔挖空区域。
  function noseCut(x, y, z) {
    if (z < 0.20 || y > -0.12 || y < -0.62) return false;
    var t = clampRange((-0.12 - y) / 0.50, 0, 1);
    var half = 0.050 + t * 0.185;
    return Math.abs(x) < half && z > 0.38 + t * 0.18;
  }
  // 判断备用点是否落入嘴部空隙。
  function mouthGap(x, y, z) {
    return z > 0.18 && y < -0.66 && y > -1.03 && Math.abs(x) < 0.30;
  }
  // 在椭球表面随机采样备用骷髅点，并排除眼鼻嘴等空洞。
  function addEllipsoidSurface(count, cx, cy, cz, rx, ry, rz, yMin, yMax, k, frontBias) {
    // made 是成功写入数量，guard 防止随机采样陷入无限循环。
    var made = 0, guard = 0;
    while (made < count && guard < count * 8) {
      guard++;
      var theta = frontBias
        ? (-Math.PI * 0.07 + Math.random() * Math.PI * 1.14)
        : (Math.random() * Math.PI * 2);
      var phi = Math.acos(1 - Math.random() * 2);
      var sx = Math.sin(phi) * Math.cos(theta);
      var sy = Math.cos(phi);
      var sz = Math.sin(phi) * Math.sin(theta);
      var x = cx + sx * rx * (0.96 + Math.max(0, -sy) * 0.12);
      var y = cy + sy * ry;
      var z = cz + sz * rz;
      if (y < yMin || y > yMax) continue;
      if (eyeCut(x, y, z, -1) || eyeCut(x, y, z, 1) || noseCut(x, y, z) || mouthGap(x, y, z)) continue;
      // 适度挖掉颧骨区域，让备用模型轮廓更接近骷髅。
      var cheekCarve = z > 0.18 && y < -0.18 && y > -0.66 && Math.abs(x) > 0.26 && Math.abs(x) < 0.58 && Math.random() < 0.36;
      if (cheekCarve) continue;
      skullPushPoint(pos, seed, kind, x, y, z, k + Math.random() * 0.08);
      made++;
    }
  }

  // 备用头骨上半部分。
  addEllipsoidSurface(3150, 0, 0.46, 0.00, 0.93, 0.88, 0.58, -0.16, 1.35, 0.055, true);
  // 备用面部和颌骨主体。
  addEllipsoidSurface(2100, 0, -0.34, 0.10, 0.70, 0.66, 0.46, -0.95, 0.14, 0.10, true);
  // 备用下颌环形点。
  for (var j = 0; j < 1450; j++) {
    var a = Math.random() * Math.PI * 2;
    var v = Math.random();
    var y = -1.16 + v * 0.48;
    var taper = clampRange((y + 1.16) / 0.48, 0, 1);
    var rx = 0.32 + taper * 0.31;
    var rz = 0.22 + taper * 0.18;
    var x = Math.cos(a) * rx;
    var z = 0.22 + Math.sin(a) * rz;
    if (mouthGap(x, y, z)) continue;
    if (y > -0.94 && Math.abs(x) < 0.22 && z > 0.18) continue;
    skullPushPoint(pos, seed, kind, x, y, z, 0.15 + Math.random() * 0.10);
  }

  // 备用眼眶、眉骨和颧骨曲线。
  [-1, 1].forEach(function(side){
    var cx = side * 0.38;
    skullPushCurve(pos, seed, kind, 520, function(t){
      var a = t * Math.PI * 2;
      var px = Math.cos(a) * (0.345 + Math.sin(a * 2.0) * 0.012);
      var py = Math.sin(a) * (0.205 + Math.cos(a * 2.0) * 0.010);
      var r = rotate2(px, py, -side * 0.10);
      return {
        x: cx + r.x,
        y: 0.02 + r.y - Math.max(0, Math.cos(a)) * 0.018,
        z: 0.72 + Math.sin(a * 2.0) * 0.030
      };
    }, 0.96, 0.010);
    skullPushCurve(pos, seed, kind, 330, function(t){
      var x = side * (0.13 + t * 0.58);
      var y = 0.245 - t * 0.085 + Math.sin(t * Math.PI) * 0.055;
      return { x:x, y:y, z:0.66 + Math.sin(t * Math.PI) * 0.055 };
    }, 0.98, 0.010);
    skullPushCurve(pos, seed, kind, 300, function(t){
      return {
        x: side * (0.30 + t * 0.47),
        y: -0.18 - t * 0.25 + Math.sin(t * Math.PI) * 0.070,
        z: 0.69 - t * 0.095
      };
    }, 0.84, 0.012);
    skullPushCurve(pos, seed, kind, 330, function(t){
      return {
        x: side * (0.62 - t * 0.20),
        y: -0.28 - t * 0.55 + Math.sin(t * Math.PI) * 0.065,
        z: 0.50 + Math.sin(t * Math.PI) * 0.070
      };
    }, 0.72, 0.014);
  });

  // 备用额头横向轮廓线。
  skullPushCurve(pos, seed, kind, 360, function(t){
    var x = -0.72 + t * 1.44;
    return { x:x, y:0.235 - Math.abs(x) * 0.055 + Math.sin(t * Math.PI) * 0.035, z:0.62 + Math.sin(t * Math.PI) * 0.040 };
  }, 0.86, 0.012);
  // 备用鼻梁两侧线。
  [-1, 1].forEach(function(side){
    skullPushCurve(pos, seed, kind, 260, function(t){
      return { x:side * (0.035 + t * 0.205), y:-0.15 - t * 0.43, z:0.79 - t * 0.035 };
    }, 0.98, 0.007);
  });
  // 备用上颌和嘴部边界。
  skullPushCurve(pos, seed, kind, 240, function(t){
    var x = -0.25 + t * 0.50;
    return { x:x, y:-0.62 + Math.sin(t * Math.PI) * 0.030, z:0.70 };
  }, 0.86, 0.008);
  // 备用下颌弧线。
  skullPushCurve(pos, seed, kind, 420, function(t){
    var a = Math.PI + t * Math.PI;
    return { x: Math.cos(a) * 0.50, y: -0.98 + Math.sin(a) * 0.205, z: 0.46 + Math.sin(t * Math.PI) * 0.075 };
  }, 0.82, 0.014);
  // 备用上牙床。
  skullPushCurve(pos, seed, kind, 360, function(t){
    var x = -0.39 + t * 0.78;
    return { x:x, y:-0.70 + Math.sin(t * Math.PI) * 0.018, z:0.73 };
  }, 0.96, 0.006);
  // 备用下牙床。
  skullPushCurve(pos, seed, kind, 320, function(t){
    var x = -0.36 + t * 0.72;
    return { x:x, y:-1.005 - Math.sin(t * Math.PI) * 0.018, z:0.70 };
  }, 0.78, 0.008);
  // 备用牙齿竖向线。
  for (var tooth = -4; tooth <= 4; tooth++) {
    var tx = tooth * 0.082;
    var height = tooth === 0 ? 0.30 : (0.25 + (4 - Math.abs(tooth)) * 0.012);
    skullPushCurve(pos, seed, kind, 58, function(t){
      return { x: tx + Math.sin(t * Math.PI) * 0.006, y: -0.715 - t * height, z: 0.735 - t * 0.020 };
    }, 0.94, 0.004);
  }
  // 备用头骨外轮廓弧线。
  skullPushCurve(pos, seed, kind, 520, function(t){
    var a = Math.PI * 0.12 + t * Math.PI * 0.76;
    return { x: Math.cos(a) * 0.98, y: 0.42 + Math.sin(a) * 0.92, z: 0.48 + Math.sin(t * Math.PI) * 0.10 };
  }, 0.70, 0.012);
  // 备用下颌底部椭圆。
  skullPushCurve(pos, seed, kind, 360, function(t){
    var a = t * Math.PI * 2;
    return { x: Math.cos(a) * 0.52, y: -1.19 + Math.sin(a) * 0.082, z: 0.24 + Math.sin(a * 2.0) * 0.028 };
  }, 0.72, 0.010);
  }

  // 正常路径从资源生成几何；备用路径从程序化数组生成几何。
  var geo = asset ? buildSkullParticleGeometryFromAsset(asset) : new THREE.BufferGeometry();
  if (!asset) {
    geo.setAttribute('position', new THREE.BufferAttribute(new Float32Array(pos), 3));
    geo.setAttribute('seed', new THREE.BufferAttribute(new Float32Array(seed), 1));
    geo.setAttribute('kind', new THREE.BufferAttribute(new Float32Array(kind), 1));
  }
  // 骷髅材质包含独立的下颌、闪光和调色 uniform。
  var mat = new THREE.ShaderMaterial({
    uniforms: {
      uMap: { value: dotTexture },
      uTime: uniforms.uTime,
      uPixel: uniforms.uPixel,
      uBass: uniforms.uBass,
      uMid: uniforms.uMid,
      uTreble: uniforms.uTreble,
      uBeat: uniforms.uBeat,
      uJawOpen: { value: 0 },
      uSkullFlash: { value: 0 },
      uPointScale: uniforms.uPointScale,
      uBloomStrength: uniforms.uBloomStrength,
      uColorBoost: uniforms.uColorBoost,
      uOpacity: { value: 0 },
      uColorA: { value: new THREE.Color('#b8ae98') },
      uColorB: { value: new THREE.Color('#fff4d8') },
      uShadow: { value: new THREE.Color('#100d0d') },
      uLight: { value: new THREE.Color('#ffe3a0') }
    },
    vertexShader: [
      'precision highp float;',
      'attribute float seed,kind;',
      'uniform float uTime,uPixel,uPointScale,uBloomStrength,uColorBoost;',
      'uniform float uBass,uMid,uTreble,uBeat,uJawOpen,uSkullFlash;',
      'varying float vKind,vLight,vRim,vAmp,vDensity,vFlash;',
      'void main(){',
      '  vec3 pos = position;',
      '  float jawGroup = step(1.0, kind);',
      '  float boneKind = fract(kind);',
      '  vKind = boneKind;',
      '  vec3 n = normalize(vec3(position.x * 0.82, position.y * 0.68, position.z * 1.22 + 0.16));',
      '  float toothBand = smoothstep(0.48, 0.70, position.z) * (1.0 - smoothstep(0.27, 0.48, abs(position.x))) * (1.0 - smoothstep(0.18, 0.46, abs(position.y + 0.72)));',
      '  float toothNoise = fract(sin(seed * 21.731 + floor((position.x + 0.52) * 21.0) * 5.137) * 43758.5453);',
      '  pos.y += toothBand * (toothNoise - 0.5) * 0.020;',
      '  pos.z += toothBand * (fract(sin(seed * 17.923 + position.y * 31.0) * 24634.6345) - 0.5) * 0.012;',
      '  float jawSidePull = jawGroup * smoothstep(-0.42, -1.06, position.y) * smoothstep(0.24, 0.62, abs(position.x)) * (1.0 - smoothstep(0.78, 1.04, abs(position.x))) * smoothstep(0.16, 0.70, position.z);',
      '  pos.x *= 1.0 - jawSidePull * 0.10;',
      '  float fallbackJaw = smoothstep(-0.48, -0.90, position.y) * smoothstep(0.08, 0.52, position.z) * (1.0 - smoothstep(0.62, 0.96, abs(position.x)));',
      '  float jawMask = jawGroup;',
      '  float jawSideAnchor = smoothstep(0.36, 0.66, abs(position.x)) * (1.0 - smoothstep(0.78, 0.98, abs(position.x))) * smoothstep(-0.34, -0.74, position.y) * (1.0 - smoothstep(0.62, 0.86, position.z));',
      '  float jawMotion = jawMask * (1.0 - jawSideAnchor * 0.32);',
      '  vec2 jawHinge = vec2(-0.45, 0.18);',
      '  float jawAngle = uJawOpen * 0.52 * jawMotion;',
      '  float jc = cos(jawAngle);',
      '  float js = sin(jawAngle);',
      '  vec2 jr = pos.yz - jawHinge;',
      '  vec2 openedJaw = vec2(jr.x * jc - jr.y * js, jr.x * js + jr.y * jc) + jawHinge;',
      '  pos.yz = mix(pos.yz, openedJaw, jawMotion);',
      '  float jawDrop = jawMotion * smoothstep(-0.32, -0.88, position.y) * (0.58 + smoothstep(0.18, 0.62, abs(position.x)) * 0.04);',
      '  float openDrive = clamp(uJawOpen, 0.0, 1.25);',
      '  pos.y -= jawDrop * (0.038 + openDrive * 0.100);',
      '  pos.z += jawDrop * (0.003 + openDrive * 0.014);',
      '  float ampDrive = smoothstep(0.20, 0.82, uBass * 0.44 + uMid * 0.22 + uBeat * 0.72);',
      '  float ampPhase = 0.50 + 0.50 * sin(uTime * (1.05 + uMid * 0.30) + seed * 6.2831);',
      '  vFlash = clamp(uSkullFlash * (0.68 + ampPhase * 0.32), 0.0, 1.0);',
      '  vAmp = clamp(ampDrive * 0.045 + vFlash * 0.92 + uTreble * 0.012, 0.0, 1.0);',
      '  vec4 mv = modelViewMatrix * vec4(pos, 1.0);',
      '  float dist = max(0.55, -mv.z);',
      '  vec3 vn = normalize(normalMatrix * n);',
      '  vec3 keyDir = normalize(vec3(-0.48, 0.64, 0.60));',
      '  vec3 lowDir = normalize(vec3(-0.10, -0.78, 0.34));',
      '  vec3 fillDir = normalize(vec3(0.36, -0.04, 0.64));',
      '  vec3 rimDir = normalize(vec3(0.88, 0.18, -0.44));',
      '  float key = pow(max(dot(vn, keyDir), 0.0), 1.18);',
      '  float low = pow(max(dot(vn, lowDir), 0.0), 1.34) * 0.10;',
      '  float fill = max(dot(vn, fillDir), 0.0) * 0.055;',
      '  float gothicShadow = smoothstep(-0.10, 0.36, dot(vn, normalize(vec3(0.44, -0.06, -0.58))));',
      '  float dentalLift = smoothstep(0.48, 0.72, position.z) * (1.0 - smoothstep(0.30, 0.54, abs(position.x))) * (1.0 - smoothstep(0.18, 0.48, abs(position.y + 0.70))) * (0.62 + toothNoise * 0.20);',
      '  vRim = pow(max(dot(vn, rimDir), 0.0), 2.50) * (0.24 + uBloomStrength * 0.08 + vFlash * 0.62);',
      '  float dust = fract(sin(seed * 13.871 + position.x * 19.7 + position.y * 7.1) * 43758.5453);',
      '  vDensity = clamp(0.30 + key * 0.70 + vRim * 0.24 - gothicShadow * 0.24 + dust * 0.025 + vFlash * 0.08, 0.16, 1.20);',
      '  vLight = clamp(0.115 + key * 1.02 + low + fill + dentalLift * 0.20 + boneKind * 0.070 + vAmp * 0.56 - gothicShadow * 0.08, 0.035, 1.72);',
      '  float scaleCtl = clamp(uPointScale, 0.48, 2.35);',
      '  float size = (0.035 + boneKind * 0.026) * (0.84 + vDensity * 0.22 + vLight * 0.13 + uBloomStrength * 0.030 + vFlash * 0.18);',
      '  gl_PointSize = clamp(size * uPixel * scaleCtl * 128.0 / dist, 0.95, 7.60);',
      '  gl_Position = projectionMatrix * mv;',
      '}'
    ].join('\n'),
    fragmentShader: [
      'precision highp float;',
      'uniform sampler2D uMap;',
      'uniform vec3 uColorA,uColorB,uShadow,uLight;',
      'uniform float uOpacity,uBloomStrength,uColorBoost;',
      'varying float vKind,vLight,vRim,vAmp,vDensity,vFlash;',
      'void main(){',
      '  vec4 tex = texture2D(uMap, gl_PointCoord);',
      '  if(tex.a < 0.070) discard;',
      '  float contrast = clamp(uColorBoost, 0.50, 2.00);',
      '  float lit = clamp(pow(vLight, mix(1.18, 0.74, (contrast - 0.50) / 1.50)), 0.0, 1.28);',
      '  vec3 bone = mix(uColorA, uColorB, clamp((vKind - 0.34) * 2.0 + lit * 0.18, 0.0, 1.0));',
      '  vec3 col = mix(uShadow, bone, clamp(lit, 0.0, 1.0));',
      '  col = mix(col, uLight, clamp(vRim * (0.14 + uBloomStrength * 0.035 + vFlash * 0.40), 0.0, 0.54));',
      '  col = mix(col, uLight, clamp(vAmp * (0.09 + uBloomStrength * 0.025) + vFlash * 0.56, 0.0, 0.68));',
      '  float alpha = tex.a * uOpacity * clamp(0.20 + lit * 0.44 + vDensity * 0.40 + vRim * 0.10 + vFlash * 0.46, 0.12, 1.56);',
      '  gl_FragColor = vec4(col, alpha);',
      '}'
    ].join('\n'),
    transparent: true,
    depthWrite: false,
    depthTest: true,
    blending: THREE.NormalBlending
  });
  // 创建骷髅粒子对象，默认隐藏，进入预设后再淡入。
  skullParticleGroup = new THREE.Points(geo, mat);
  skullParticleGroup.frustumCulled = false;
  skullParticleGroup.visible = false;
  // 记录点云来源，便于调试资源路径和备用路径。
  skullParticleGroup.userData.source = asset ? 'asset' : 'fallback';
  // 应用基础位置、缩放和旋转。
  skullParticleGroup.position.set(SKULL_MODEL_BASE_POSITION.x, SKULL_MODEL_BASE_POSITION.y, SKULL_MODEL_BASE_POSITION.z);
  skullParticleGroup.scale.setScalar(SKULL_MODEL_SCALE);
  skullParticleGroup.rotation.x = SKULL_MODEL_BASE_ROTATION_X;
  skullParticleGroup.rotation.y = SKULL_MODEL_BASE_ROTATION_Y;
  skullParticleGroup.renderOrder = 32;
  // 创建后立即同步一次当前色调。
  syncSkullParticleColors();
  scene.add(skullParticleGroup);
  return skullParticleGroup;
}
// 判断骷髅预设是否处于歌单架侧边组合构图。
function isSkullShelfCompositionActive() {
  // 只有骷髅预设才进入这套构图判断。
  if (!(fx && fx.preset === SKULL_PRESET_INDEX)) return false;
  // 歌单架必须处于 side 模式。
  if (!shelfManager || !shelfManager.getMode || shelfManager.getMode() !== 'side') return false;
  // 固定打开或可见度较高时视为组合构图。
  if (shelfPinnedOpen || shelfVisibility > 0.18) return true;
  // 二级内容打开时也需要给歌单架留出构图空间。
  return !!(shelfManager.hasOpenContent && shelfManager.hasOpenContent());
}
// 离开骷髅预设时清理残留的透明度、闪光和下颌状态。
function clearSkullPresetResidue() {
  skullParticleOpacity = 0;
  skullAmpPulse = 0;
  skullBeatFlash = 0;
  skullJawOpen = 0;
  skullCameraBlend = 0;
  // 骷髅层尚未创建时只重置状态即可。
  if (!skullParticleGroup) return;
  skullParticleGroup.visible = false;
  if (skullParticleGroup.material && skullParticleGroup.material.uniforms) {
    if (skullParticleGroup.material.uniforms.uOpacity) skullParticleGroup.material.uniforms.uOpacity.value = 0;
    if (skullParticleGroup.material.uniforms.uJawOpen) skullParticleGroup.material.uniforms.uJawOpen.value = 0;
    if (skullParticleGroup.material.uniforms.uSkullFlash) skullParticleGroup.material.uniforms.uSkullFlash.value = 0;
  }
}
// 重置骷髅预设视图和相关歌词锁定状态。
function resetSkullPresetView(immediate, opts) {
  // opts 控制是否平滑、是否保留歌词锁定。
  opts = opts || {};
  // 非骷髅预设不处理。
  if (!(fx && fx.preset === SKULL_PRESET_INDEX)) return;
  // 重置滚轮缩放目标。
  skullWheelZoomTarget = 0;
  // 非平滑重置时当前缩放也立即归零。
  if (!opts.smooth) skullWheelZoom = 0;
  // 强制相机进入骷髅构图混合。
  skullCameraBlend = Math.max(skullCameraBlend, 1);
  // 需要时解除嘴部歌词锁定，并请求歌词相机快速贴合。
  if (!opts.keepLyricLock && typeof stageLyrics !== 'undefined' && stageLyrics && stageLyrics.group && stageLyrics.group.userData) stageLyrics.group.userData.skullMouthLocked = false;
  if (!opts.keepLyricLock && typeof requestStageLyricCameraSnap === 'function') requestStageLyricCameraSnap(10);
  if (!immediate || !skullParticleGroup) return;
  // 立即重置时根据当前歌单架状态选择普通或侧边构图。
  var shelfComposition = isSkullShelfCompositionActive();
  skullShelfCameraMix = shelfComposition ? 1 : 0;
  skullParticleGroup.position.set(shelfComposition ? -1.18 : SKULL_MODEL_BASE_POSITION.x, shelfComposition ? 0.32 : SKULL_MODEL_BASE_POSITION.y, SKULL_MODEL_BASE_POSITION.z);
  skullParticleGroup.scale.setScalar(shelfComposition ? 3.02 : SKULL_MODEL_SCALE);
  skullParticleGroup.rotation.set(SKULL_MODEL_BASE_ROTATION_X, SKULL_MODEL_BASE_ROTATION_Y, 0);
  skullParticleGroup.updateMatrixWorld(true);
  if (camera && typeof setSkullCameraTargetVectors === 'function') {
    // 竖屏和横屏使用不同相机目标，保证骷髅位于安全区域。
    var portrait = innerHeight > innerWidth * 1.08;
    setSkullCameraTargetVectors(skullCameraTargetPos, skullCameraTargetLook, portrait, shelfComposition, 0);
    camera.position.copy(skullCameraTargetPos);
    skullCameraMixedLook.copy(skullCameraTargetLook);
    camera.lookAt(skullCameraMixedLook);
    camera.updateProjectionMatrix();
  }
}
// 计算骷髅模型的慢速呼吸漂移。
function skullBreathOffset(t, shelfComposition) {
  // 歌单架组合构图下减少漂移，避免和侧栏产生视觉冲突。
  var strength = shelfComposition ? 0.70 : 1.0;
  return {
    x: strength * (Math.sin(t * 0.33 + 1.7) * 0.028 + Math.sin(t * 0.61 + 0.4) * 0.010),
    y: strength * (Math.sin(t * 0.38 + 0.2) * 0.036 + Math.sin(t * 0.83 + 2.1) * 0.012),
    z: strength * (Math.sin(t * 0.24 + 2.6) * 0.026)
  };
}
// 写入骷髅预设目标相机位置和注视点。
function setSkullCameraTargetVectors(pos, look, portrait, shelfComposition, zoom) {
  // zoom 来自滚轮，缺省为 0。
  zoom = Number(zoom) || 0;
  if (shelfComposition) {
    // 侧边歌单架构图下相机更靠后，并把骷髅留在主视觉安全区。
    pos.set(portrait ? -0.06 : 0.00, portrait ? -2.36 : -2.50, (portrait ? 4.88 : 4.96) + zoom * 0.78);
    look.set(portrait ? -0.04 : 0.00, portrait ? -0.26 : -0.20, 0.03);
    return;
  }
  // 普通构图下骷髅居中，竖屏略微调整高度。
  pos.set(0.00, portrait ? -2.38 : -2.52, (portrait ? 4.92 : 4.98) + zoom);
  look.set(0.00, portrait ? -0.28 : -0.20, 0.02);
}
// 每帧把相机平滑混合到骷髅预设专属构图。
function applySkullCameraPose(dt) {
  // 自由相机正在接管时不覆盖用户视角。
  if (freeCamera && (freeCamera.active || freeCamera.locked || freeCamera.resetTween)) return;
  // 只有骷髅预设激活时相机混合目标为 1。
  var active = fx && fx.preset === SKULL_PRESET_INDEX;
  skullCameraBlend += ((active ? 1 : 0) - skullCameraBlend) * Math.min(1, dt * (active ? 4.8 : 7.2));
  if (skullCameraBlend < 0.002) return;
  // 滚轮缩放使用缓动，避免相机突变。
  skullWheelZoom += (skullWheelZoomTarget - skullWheelZoom) * Math.min(1, dt * 8.0);
  // 根据视口比例选择竖屏参数。
  var portrait = innerHeight > innerWidth * 1.08;
  // 歌单架打开时混合到侧边构图。
  var shelfComposition = isSkullShelfCompositionActive();
  var shelfMixTarget = shelfComposition ? 1 : 0;
  skullShelfCameraMix += (shelfMixTarget - skullShelfCameraMix) * Math.min(1, dt * (shelfMixTarget > skullShelfCameraMix ? 4.6 : 5.8));
  if (Math.abs(skullShelfCameraMix - shelfMixTarget) < 0.002) skullShelfCameraMix = shelfMixTarget;
  setSkullCameraTargetVectors(skullCameraBasePos, skullCameraBaseLook, portrait, false, skullWheelZoom);
  setSkullCameraTargetVectors(skullCameraShelfPos, skullCameraShelfLook, portrait, true, skullWheelZoom);
  // 在普通构图和歌单架构图之间插值。
  skullCameraTargetPos.copy(skullCameraBasePos).lerp(skullCameraShelfPos, skullShelfCameraMix);
  skullCameraTargetLook.copy(skullCameraBaseLook).lerp(skullCameraShelfLook, skullShelfCameraMix);
  camera.position.lerp(skullCameraTargetPos, skullCameraBlend);
  skullCameraMixedLook.set(orbit.lookAt.x, orbit.lookAt.y, orbit.lookAt.z).lerp(skullCameraTargetLook, skullCameraBlend);
  camera.lookAt(skullCameraMixedLook);
  camera.updateProjectionMatrix();
}
// 每帧更新骷髅粒子可见性、下颌、闪光、缩放和旋转。
function updateSkullParticleLayer(dt) {
  // 只在骷髅预设下激活。
  var active = fx && fx.preset === SKULL_PRESET_INDEX;
  if (active && !skullParticleAsset.data && !skullParticleAsset.failed) {
    // 首次进入时异步加载点云资源，本帧先返回。
    loadSkullParticleAsset();
    return;
  }
  // 资源未加载成功时不创建粒子层。
  if (active && !skullParticleAsset.data) return;
  // 激活时按需创建粒子层。
  if (active) createSkullParticleLayer();
  if (!skullParticleGroup) return;
  // 透明度按激活状态缓入缓出。
  var target = active ? 1 : 0;
  skullParticleOpacity += (target - skullParticleOpacity) * Math.min(1, dt * (active ? 3.2 : 2.4));
  if (skullParticleOpacity < 0.006 && !active) {
    skullParticleGroup.visible = false;
    return;
  }
  skullParticleGroup.visible = true;
  // 透明度受全局强度影响，但限制在合理范围。
  skullParticleGroup.material.uniforms.uOpacity.value = skullParticleOpacity * clampRange(0.78 + (fx.intensity || 0.85) * 0.18, 0.56, 1.0);
  // 根据节拍脉冲计算短促闪光。
  var beatTransient = clampRange(Math.max(0, beatPulse - 0.16) / 0.84, 0, 1.35);
  var flashTarget = clampRange(Math.pow(beatTransient, 1.34) * 1.08 + Math.max(0, bass - 0.60) * 0.18 * beatTransient, 0, 1);
  skullBeatFlash += (flashTarget - skullBeatFlash) * Math.min(1, dt * (flashTarget > skullBeatFlash ? 24.0 : 6.2));
  if (skullParticleGroup.material.uniforms.uSkullFlash) skullParticleGroup.material.uniforms.uSkullFlash.value = skullBeatFlash;
  // 下颌张开随低频、节拍闪光和慢速呼吸变化。
  var jawTarget = clampRange(0.60 + (0.5 + 0.5 * Math.sin(uniforms.uTime.value * 0.50)) * 0.050 + bass * 0.060 + skullBeatFlash * 0.090, 0.52, 0.88);
  skullJawOpen += (jawTarget - skullJawOpen) * Math.min(1, dt * (jawTarget > skullJawOpen ? 7.8 : 3.4));
  if (skullParticleGroup.material.uniforms.uJawOpen) skullParticleGroup.material.uniforms.uJawOpen.value = skullJawOpen;
  // 组合构图会改变模型位置和缩放。
  var shelfComposition = isSkullShelfCompositionActive();
  var shelfMix = clampRange(skullShelfCameraMix || (shelfComposition ? 1 : 0), 0, 1);
  var drift = skullBreathOffset(uniforms.uTime.value, shelfComposition);
  // 音频脉冲影响模型整体缩放。
  var ampTarget = clampRange(bass * 0.006 + mid * 0.004 + skullBeatFlash * 0.070, 0, 0.090);
  skullAmpPulse += (ampTarget - skullAmpPulse) * Math.min(1, dt * (ampTarget > skullAmpPulse ? 11.0 : 4.0));
  var shelfScale = 3.02;
  // 缩放同时考虑歌单架构图、音频脉冲和滚轮距离。
  var targetScale = (SKULL_MODEL_SCALE + (shelfScale - SKULL_MODEL_SCALE) * shelfMix) * (1 + skullAmpPulse) * clampRange(1 - skullWheelZoom * 0.055, 0.92, 1.08);
  // 歌单架构图下的目标位置。
  var shelfX = -1.18;
  var shelfY = 0.32;
  // 目标位置叠加呼吸漂移。
  var targetX = (SKULL_MODEL_BASE_POSITION.x + (shelfX - SKULL_MODEL_BASE_POSITION.x) * shelfMix) + drift.x;
  var targetY = (SKULL_MODEL_BASE_POSITION.y + (shelfY - SKULL_MODEL_BASE_POSITION.y) * shelfMix) + drift.y;
  var targetZ = SKULL_MODEL_BASE_POSITION.z + drift.z;
  skullParticleGroup.position.x += (targetX - skullParticleGroup.position.x) * Math.min(1, dt * 4.2);
  skullParticleGroup.position.y += (targetY - skullParticleGroup.position.y) * Math.min(1, dt * 4.8);
  skullParticleGroup.position.z += (targetZ - skullParticleGroup.position.z) * Math.min(1, dt * 4.2);
  skullParticleGroup.scale.x += (targetScale - skullParticleGroup.scale.x) * Math.min(1, dt * 4.6);
  skullParticleGroup.scale.y = skullParticleGroup.scale.x;
  skullParticleGroup.scale.z = skullParticleGroup.scale.x;
  // 非居中锁定时，头部视差和粒子旋转共同影响骷髅朝向。
  var targetRotY = SKULL_MODEL_BASE_ROTATION_Y + (orbit.centerLocked ? 0 : (headParallax.active ? headParallax.x * 0.5 : 0) + particleRotation.y);
  var targetRotX = SKULL_MODEL_BASE_ROTATION_X + (orbit.centerLocked ? 0 : (headParallax.active ? -headParallax.y * 0.35 : 0) + particleRotation.x);
  var rotEase = Math.min(1, dt * 7.4);
  skullParticleGroup.rotation.y += (targetRotY - skullParticleGroup.rotation.y) * rotEase;
  skullParticleGroup.rotation.x += (targetRotX - skullParticleGroup.rotation.x) * rotEase;
  skullParticleGroup.rotation.z += (0 - skullParticleGroup.rotation.z) * Math.min(1, dt * 6.0);
}

// ============================================================
//  封面背面粒子层 (v7.2)
//   - 独立 Points, 放在 z=-1.5 (主封面平面背面)
//   - 颜色取自封面镜像 UV
//   - 慢呼吸 + 小幅 noise 漂移
//   - 跟主粒子同步旋转 (在主循环里赋值)
//   - 视角转到背面才能看到 — 不需要手动控制 visible
// ============================================================
// 封面背面粒子数量。
var BACK_COVER_COUNT = 3000;
// 背面封面 Points 容器。
var backCoverGroup = null;
// 背面封面粒子颜色数组，封面变化时会刷新。
var backCoverColorArr = null;

// 创建封面背面粒子层，用于从背面视角看到专辑颜色云。
function createBackCoverLayer() {
  // 已创建时不重复创建。
  if (backCoverGroup) return;
  // 背面层独立几何，位置、颜色、随机值和镜像 UV 分开存储。
  var bg = new THREE.BufferGeometry();
  // 背面粒子位置。
  var bp = new Float32Array(BACK_COVER_COUNT * 3);
  // 背面粒子颜色。
  var bc = new Float32Array(BACK_COVER_COUNT * 3);
  // 背面粒子随机种子。
  var br = new Float32Array(BACK_COVER_COUNT);
  // 背面粒子镜像 UV。
  var bu = new Float32Array(BACK_COVER_COUNT * 2);  // 镜像 UV 用于采样封面
  for (var i = 0; i < BACK_COVER_COUNT; i++) {
    // 每个粒子随机取封面上的一个 UV。
    var u = Math.random();
    var v = Math.random();
    // 在 PLANE_SIZE 范围内分布
    bp[i*3]   = (u - 0.5) * PLANE_SIZE;
    bp[i*3+1] = (v - 0.5) * PLANE_SIZE;
    bp[i*3+2] = -1.5 - Math.random() * 0.4;  // 在主平面后方
    bu[i*2]   = 1.0 - u;  // 镜像 X
    bu[i*2+1] = v;
    br[i] = Math.random();
    bc[i*3] = 0.7; bc[i*3+1] = 0.6; bc[i*3+2] = 0.8;  // 占位
  }
  bg.setAttribute('position', new THREE.BufferAttribute(bp, 3));
  bg.setAttribute('aColor',   new THREE.BufferAttribute(bc, 3));
  bg.setAttribute('aRand',    new THREE.BufferAttribute(br, 1));
  bg.setAttribute('aUv',      new THREE.BufferAttribute(bu, 2));

  // 背面层顶点 shader 负责慢速呼吸和低频扰动。
  var vs = `
    precision highp float;
    uniform float uTime, uBass, uPixel, uAlpha;
    attribute vec3 aColor;
    attribute vec2 aUv;
    attribute float aRand;
    varying vec3 vC;
    varying float vA;
    void main(){
      vec3 pos = position;
      // 缓慢呼吸
      pos.x += sin(uTime * 0.20 + aRand * 8.0) * 0.20;
      pos.y += cos(uTime * 0.18 + aRand * 6.0) * 0.22;
      pos.z += sin(uTime * 0.12 + aRand * 5.0) * 0.18 + uBass * 0.12 * sin(aRand * 11.0);
      vC = aColor;
      vec4 mvPos = modelViewMatrix * vec4(pos, 1.0);
      float dist = -mvPos.z;
      vA = clamp(0.30 + 0.4 * sin(uTime * 0.6 + aRand * 5.0), 0.10, 0.65);
      float sz = clamp(46.0 / max(0.5, dist), 1.4, 4.5);
      gl_PointSize = sz * uPixel;
      gl_Position = projectionMatrix * mvPos;
    }
  `;
  // 背面层片元 shader 复用圆点纹理并乘以整体透明度。
  var fs = `
    precision highp float;
    uniform sampler2D uDotTex;
    uniform float uAlpha;
    varying vec3 vC;
    varying float vA;
    void main(){
      vec4 tex = texture2D(uDotTex, gl_PointCoord);
      if (tex.a < 0.02) discard;
      gl_FragColor = vec4(vC, tex.a * vA * uAlpha);
    }
  `;
  // 背面层材质使用正常混合，避免背面粒子过亮。
  var mat = new THREE.ShaderMaterial({
    uniforms: {
      uTime: uniforms.uTime,
      uBass: uniforms.uBass,
      uPixel: uniforms.uPixel,
      uDotTex: uniforms.uDotTex,
      uAlpha: uniforms.uAlpha,
    },
    vertexShader: vs, fragmentShader: fs,
    transparent:true, depthWrite:false, blending: THREE.NormalBlending,
  });
  // 创建背面粒子对象并缓存颜色数组引用。
  backCoverGroup = new THREE.Points(bg, mat);
  backCoverGroup.frustumCulled = false;
  backCoverColorArr = bc;
  scene.add(backCoverGroup);
}

// 销毁封面背面粒子层并释放资源。
function destroyBackCoverLayer() {
  // 未创建时无需处理。
  if (!backCoverGroup) return;
  scene.remove(backCoverGroup);
  // 背面层几何和材质独占，可以直接释放。
  backCoverGroup.geometry.dispose(); backCoverGroup.material.dispose();
  backCoverGroup = null; backCoverColorArr = null;
}

// 从封面 canvas 重新采样背面粒子颜色。
function refreshBackCoverColorsFromCanvas(coverCanvas) {
  // 背面层未创建或没有封面数据时跳过。
  if (!backCoverGroup || !coverCanvas || !backCoverColorArr) return;
  // 读取封面像素数据用于 CPU 侧取色。
  var ctx = coverCanvas.getContext('2d');
  var img = ctx.getImageData(0, 0, coverCanvas.width, coverCanvas.height).data;
  // 缓存宽高，避免循环内重复访问 canvas 属性。
  var w = coverCanvas.width, h = coverCanvas.height;
  // 取得几何 attribute，刷新 aColor 后需要标记 needsUpdate。
  var attr = backCoverGroup.geometry.attributes;
  var uvA = attr.aUv.array;
  for (var i = 0; i < BACK_COVER_COUNT; i++) {
    // 使用创建时保存的镜像 UV 定位封面像素。
    var u = uvA[i*2], v = uvA[i*2+1];
    var sx = Math.floor(u * w);
    var sy = Math.floor(v * h);
    var di = (sy * w + sx) * 4;
    backCoverColorArr[i*3]   = img[di]   / 255 * 0.85;
    backCoverColorArr[i*3+1] = img[di+1] / 255 * 0.85;
    backCoverColorArr[i*3+2] = img[di+2] / 255 * 0.85;
  }
  attr.aColor.needsUpdate = true;
}
// 浮空粒子漂移在 shader 中完成，此函数保留给主循环调用。
function updateFloatLayer(dt) {
  // 漂移已在 shader 中完成, JS 不需要每帧改 buffer
}
// 从封面随机采样颜色并刷新浮空粒子色彩。
function refreshFloatColorsFromCover(coverCanvas) {
  // 浮空层未启用或没有封面时跳过。
  if (!floatGroup || !coverCanvas) return;
  // 读取封面像素，用随机点给浮空粒子上色。
  var ctx = coverCanvas.getContext('2d');
  var img = ctx.getImageData(0, 0, coverCanvas.width, coverCanvas.height).data;
  // 缓存封面尺寸。
  var w = coverCanvas.width, h = coverCanvas.height;
  for (var i = 0; i < FLOAT_COUNT; i++) {
    // 每个浮空粒子随机取一个封面像素。
    var sx = Math.floor(Math.random() * w);
    var sy = Math.floor(Math.random() * h);
    var di = (sy * w + sx) * 4;
    floatColorArr[i*3]   = img[di]   / 255 * 0.95;
    floatColorArr[i*3+1] = img[di+1] / 255 * 0.95;
    floatColorArr[i*3+2] = img[di+2] / 255 * 0.95;
  }
  floatGroup.geometry.attributes.aColor.needsUpdate = true;
}
// 将浮空粒子颜色恢复成空闲白色系。
function resetFloatColorsToIdle() {
  // 浮空层未创建时无需恢复。
  if (!floatGroup || !floatColorArr) return;
  for (var i = 0; i < FLOAT_COUNT; i++) {
    // 用索引生成稳定的轻微明度差异，避免全白过平。
    var white = 0.88 + (i % 17) / 17 * 0.12;
    floatColorArr[i*3] = white;
    floatColorArr[i*3+1] = white;
    floatColorArr[i*3+2] = white;
  }
  floatGroup.geometry.attributes.aColor.needsUpdate = true;
}



// ===== js/03-stage-lyrics.js =====

// ============================================================
//  舞台歌词系统 v9 — Three.js 文字平面, 跟随专辑粒子 3D 运动
// ============================================================
// 舞台歌词运行期状态，集中保存当前歌词 mesh、退出动画、发光状态和歌词色板。
var stageLyrics = {
  // Three.js 分组，所有歌词相关对象都会挂在这里。
  group: null,
  // 当前正在显示的歌词 mesh。
  current: null,
  // 正在淡出的上一句歌词 mesh 队列。
  outgoing: [],
  // 当前歌词在解析结果中的索引。
  currentIdx: -1,
  // 当前歌词文本，用于避免重复创建相同内容。
  currentText: '',
  // 高频触发的歌词高亮辉光强度。
  highBloom: 0,
  // 节拍触发的歌词发光强度。
  beatGlow: 0,
  // 辉光跟随的横向偏移。
  glowFollowX: 0,
  // 辉光跟随的纵向偏移。
  glowFollowY: 0,
  // 辉光跟随的轻微旋转。
  glowFollowRoll: 0,
  // 当前实际用于歌词绘制的色板。
  palette: {
    primary: '#d6f8ff',
    secondary: '#9cffdf',
    highlight: '#eef7ff',
    shadow: 'rgba(2,8,12,0.42)',
    glow: 'rgba(143,233,255,0.34)',
  },
  // 从封面提取出的基础色板，自动色模式会参考它。
  coverPalette: {
    primary: '#d6f8ff',
    secondary: '#9cffdf',
    highlight: '#eef7ff',
    shadow: 'rgba(2,8,12,0.42)',
    glow: 'rgba(143,233,255,0.34)',
  },
  // 歌词后方的星河粒子对象。
  starRiver: null,
  // 星河粒子带宽度，会随歌词宽度平滑变化。
  starRiverWidth: 4.2,
  // 星河粒子带高度，会随歌词高度平滑变化。
  starRiverHeight: 0.58,
  // 相机锁定模式下的歌词适配缩放。
  lockFitScale: 1,
  // 请求歌词相机短暂贴合的剩余帧数。
  snapCameraLockFrames: 0,
};
// 歌词阳光色，作为部分高亮和辉光计算的暖色基准。
var lyricSunColor = new THREE.Color(0xffe6a4);
// 歌词强高亮阳光色。
var lyricSunHotColor = new THREE.Color(0xfff4cc);
// 歌词布局使用的相机前方向。
var lyricCameraDir = new THREE.Vector3();
// 歌词布局使用的相机右方向。
var lyricCameraRight = new THREE.Vector3();
// 歌词布局使用的相机上方向。
var lyricCameraUp = new THREE.Vector3();
// 歌词相机锁定时的目标点缓存。
var lyricCameraTarget = new THREE.Vector3();
// 歌词布局基础坐标缓存。
var lyricLayoutBase = new THREE.Vector3();
// 歌词布局最终目标坐标缓存。
var lyricLayoutTarget = new THREE.Vector3();
// 封面中心的世界坐标缓存。
var lyricCoverWorldPos = new THREE.Vector3();
// 封面世界旋转缓存。
var lyricCoverWorldQuat = new THREE.Quaternion();
// 歌词基础朝向欧拉角缓存。
var lyricBaseEuler = new THREE.Euler(0, 0, 0, 'YXZ');
// 歌词倾斜欧拉角缓存。
var lyricTiltEuler = new THREE.Euler(0, 0, 0, 'YXZ');
// 歌词基础朝向四元数缓存。
var lyricBaseQuat = new THREE.Quaternion();
// 歌词倾斜四元数缓存。
var lyricTiltQuat = new THREE.Quaternion();
// 歌词最终目标四元数缓存。
var lyricTargetQuat = new THREE.Quaternion();
// 相机锁定模式下歌词最大缩放上限，避免贴屏过大。
var LYRIC_CAMERA_LOCK_MAX_SCALE = 0.80;
// 根据当前相机或传入四元数刷新歌词布局用的视图基向量。
function setStageLyricViewBasisFromCameraOrQuaternion(fallbackQuat) {
  if (fallbackQuat) {
    // 有传入四元数时，用它推导前、右、上方向。
    lyricCameraDir.set(0, 0, 1).applyQuaternion(fallbackQuat);
    lyricCameraRight.set(1, 0, 0).applyQuaternion(fallbackQuat);
    lyricCameraUp.set(0, 1, 0).applyQuaternion(fallbackQuat);
  } else if (camera) {
    // 默认从当前 Three.js 相机读取视图方向。
    camera.getWorldDirection(lyricCameraDir);
    lyricCameraRight.set(1, 0, 0).applyQuaternion(camera.quaternion);
    lyricCameraUp.set(0, 1, 0).applyQuaternion(camera.quaternion);
  } else {
    // 没有相机时使用世界坐标轴兜底。
    lyricCameraDir.set(0, 0, 1);
    lyricCameraRight.set(1, 0, 0);
    lyricCameraUp.set(0, 1, 0);
  }
  lyricCameraDir.normalize();
  lyricCameraRight.normalize();
  lyricCameraUp.normalize();
}
// 按相机视图基向量对歌词目标点叠加局部偏移。
function applyStageLyricLayoutOffset(target, x, y, z) {
  return target
    .addScaledVector(lyricCameraRight, x || 0)
    .addScaledVector(lyricCameraUp, y || 0)
    .addScaledVector(lyricCameraDir, z || 0);
}
// 基于基础朝向和用户倾斜角计算歌词目标朝向。
function stageLyricTargetQuaternion(baseQuat, tiltX, tiltY) {
  // 用户倾斜参数以角度保存，这里转换为弧度欧拉角。
  lyricTiltEuler.set((tiltX || 0) * Math.PI / 180, (tiltY || 0) * Math.PI / 180, 0, 'YXZ');
  lyricTiltQuat.setFromEuler(lyricTiltEuler);
  return lyricTargetQuat.copy(baseQuat || lyricBaseQuat).multiply(lyricTiltQuat);
}
// 统计当前歌词和淡出歌词的最大世界尺寸。
function getStageLyricLockBounds() {
  // 最大宽高会用于相机锁定模式的安全缩放计算。
  var maxW = 0, maxH = 0;
  // 内部辅助函数负责读取单个歌词 mesh 的尺寸。
  function take(mesh) {
    if (!mesh || !mesh.userData || !mesh.userData.lyric) return;
    // 歌词数据中保存了 canvas 映射到世界空间后的尺寸。
    var d = mesh.userData.lyric;
    // mesh 可能正在动画缩放，需要把当前 scale 计入包围尺寸。
    var meshScale = Math.max(mesh.scale && isFinite(mesh.scale.x) ? mesh.scale.x : 1, mesh.scale && isFinite(mesh.scale.y) ? mesh.scale.y : 1);
    maxW = Math.max(maxW, (d.textWorldW || d.worldW || 6.1) * meshScale);
    maxH = Math.max(maxH, (d.textWorldH || d.worldH || 1.0) * meshScale);
  }
  take(stageLyrics.current);
  for (var i = 0; i < stageLyrics.outgoing.length; i++) take(stageLyrics.outgoing[i]);
  return { w: maxW || 5.4, h: maxH || 0.78 };
}
// 计算歌词相机锁定模式下为了完整显示歌词所需的缩放倍率。
function lyricCameraLockFit(layoutScale, layoutX, layoutY, distance) {
  // 非透视相机下无法按视锥计算，直接不缩放。
  if (!camera || !camera.isPerspectiveCamera) return 1;
  // 布局缩放需要有最小值，避免除零。
  layoutScale = Math.max(0.1, layoutScale || 1);
  // 当前相机垂直视场角。
  var fov = (camera.fov || 45) * Math.PI / 180;
  // 歌词到相机的估计距离。
  var dist = Math.max(1.4, distance || 4.85);
  // 距离处可见的世界空间高度。
  var visibleH = 2 * Math.tan(fov * 0.5) * dist;
  // 距离处可见的世界空间宽度。
  var visibleW = visibleH * (camera.aspect || (innerWidth / Math.max(1, innerHeight)) || 1.78);
  // 读取当前歌词实际包围尺寸。
  var bounds = getStageLyricLockBounds();
  // 骷髅预设需要更保守的安全区域。
  var skullSafe = !!(fx && fx.preset === SKULL_PRESET_INDEX);
  // 横向安全宽度会扣除用户偏移，避免歌词贴边。
  var safeW = Math.max(visibleW * (skullSafe ? 0.36 : 0.42), visibleW * (skullSafe ? 0.70 : 0.84) - Math.abs(layoutX || 0) * (skullSafe ? 1.36 : 1.22));
  // 纵向安全高度也会扣除用户偏移。
  var safeH = Math.max(visibleH * (skullSafe ? 0.16 : 0.18), visibleH * (skullSafe ? 0.34 : 0.44) - Math.abs(layoutY || 0) * (skullSafe ? 0.98 : 0.82));
  // 当前布局缩放后的歌词宽度。
  var scaledW = Math.max(0.01, bounds.w * layoutScale);
  // 当前布局缩放后的歌词高度。
  var scaledH = Math.max(0.01, bounds.h * layoutScale);
  // 根据宽高同时求得视口适配倍率。
  var viewportFit = Math.min(1, safeW / scaledW, safeH / scaledH);
  // 再叠加一个整体上限，避免锁定模式强行放大。
  var lockScaleCap = Math.min(1, (skullSafe ? 0.94 : LYRIC_CAMERA_LOCK_MAX_SCALE) / layoutScale);
  return clampRange(Math.min(viewportFit, lockScaleCap), skullSafe ? 0.36 : 0.42, 1);
}
// 兼容旧变量名以便其它代码不破坏
// 旧版歌词粒子对象引用，保留给历史调用点。
var lyricsParticles = null;
// 旧版歌词几何引用，保留给历史调用点。
var lyricsGeo = null;

// 三个 attribute: 源位置(随机扩散态), 目标位置(组成字), color, brightness
// 歌词粒子目标位置 A 缓存。
var lyricsAttrTargetA = null;
// 歌词粒子目标位置 B 缓存。
var lyricsAttrTargetB = null;
// 歌词粒子随机种子 attribute 缓存。
var lyricsAttrSeed = null;

// 确保舞台歌词分组存在。
function createLyricsParticles() {
  // 已创建分组时只确保星河粒子存在。
  if (stageLyrics.group) {
    ensureLyricStarRiver();
    return;
  }
  // 歌词对象统一挂在独立 Group 上，便于整体定位和隐藏。
  stageLyrics.group = new THREE.Group();
  stageLyrics.group.renderOrder = 38;
  scene.add(stageLyrics.group);
  ensureLyricStarRiver();
}

// 创建或返回歌词背后的星河粒子层。
function ensureLyricStarRiver() {
  // 歌词分组不存在时不能创建；已存在时直接返回缓存。
  if (!stageLyrics.group || stageLyrics.starRiver) return stageLyrics.starRiver;
  // 星河粒子数量固定，主要用于歌词后方细光流。
  var count = 420;
  // 星河粒子几何只保存随机种子、轨道和深度种子。
  var geo = new THREE.BufferGeometry();
  // 每个粒子的随机种子。
  var seeds = new Float32Array(count);
  // 每个粒子所在流动轨道。
  var lanes = new Float32Array(count);
  // 每个粒子的深度随机值。
  var depths = new Float32Array(count);
  for (var i = 0; i < count; i++) {
    seeds[i] = Math.random() * 1000;
    lanes[i] = Math.random();
    depths[i] = Math.random();
  }
  geo.setAttribute('seed', new THREE.BufferAttribute(seeds, 1));
  geo.setAttribute('lane', new THREE.BufferAttribute(lanes, 1));
  geo.setAttribute('depthSeed', new THREE.BufferAttribute(depths, 1));
  // 星河材质完全由 shader 生成位置和颜色，不需要每帧改几何。
  var mat = new THREE.ShaderMaterial({
    uniforms: {
      uMap: { value: dotTexture },
      uTime: uniforms.uTime,
      uPixel: uniforms.uPixel,
      uBass: uniforms.uBass,
      uBeat: uniforms.uBeat,
      uWidth: { value: stageLyrics.starRiverWidth || 4.2 },
      uHeight: { value: stageLyrics.starRiverHeight || 0.58 },
      uOpacity: { value: 0 },
      uColorA: { value: lyricThreeColor(stageLyrics.palette.secondary, '#9cffdf', 0.42) },
      uColorB: { value: lyricThreeColor(stageLyrics.palette.highlight, '#fff7d2', 0.44) }
    },
    vertexShader: [
      'precision highp float;',
      'attribute float seed,lane,depthSeed;',
      'uniform float uTime,uPixel,uBass,uBeat,uWidth,uHeight;',
      'varying float vSeed,vLane,vGlow;',
      'float hash(float n){return fract(sin(n)*43758.5453123);}',
      'void main(){',
      '  float laneBand = floor(lane * 5.0);',
      '  float laneLocal = fract(lane * 5.0);',
      '  float speed = 0.030 + hash(seed * 1.71) * 0.055 + laneBand * 0.005;',
      '  float flow = fract(hash(seed * 2.13) + uTime * speed);',
      '  float x = (flow - 0.5) * uWidth * (1.08 + hash(seed * 5.1) * 0.18);',
      '  float curve = sin(flow * 6.2831853 * (0.92 + hash(seed * 4.0) * 0.46) + seed * 0.071 + uTime * 0.34);',
      '  float breath = sin(uTime * (0.42 + hash(seed * 6.9) * 0.42) + seed * 0.093);',
      '  float y = (laneBand - 2.0) * uHeight * 0.135 + curve * uHeight * (0.20 + hash(seed * 9.0) * 0.18) + (laneLocal - 0.5) * uHeight * 0.16 + breath * uHeight * 0.10;',
      '  float z = -0.08 + (depthSeed - 0.5) * 0.44 + sin(uTime * (0.18 + hash(seed) * 0.24) + seed) * 0.08;',
      '  vec3 pos = vec3(x, y, z);',
      '  float edge = smoothstep(0.0, 0.18, flow) * (1.0 - smoothstep(0.82, 1.0, flow));',
      '  vSeed = seed;',
      '  vLane = lane;',
      '  vGlow = edge * (0.62 + 0.38 * sin(uTime * (0.9 + hash(seed * 8.0) * 0.7) + seed));',
      '  vec4 mv = modelViewMatrix * vec4(pos, 1.0);',
      '  float dist = max(0.45, -mv.z);',
      '  float size = (0.030 + hash(seed * 12.0) * 0.040 + vGlow * 0.024 + uBeat * 0.010) * (1.0 + uBass * 0.18);',
      '  gl_PointSize = clamp(size * uPixel * 120.0 / dist, 1.0, 7.2);',
      '  gl_Position = projectionMatrix * mv;',
      '}'
    ].join('\n'),
    fragmentShader: [
      'precision highp float;',
      'uniform sampler2D uMap;',
      'uniform vec3 uColorA,uColorB;',
      'uniform float uOpacity,uTime,uBeat;',
      'varying float vSeed,vLane,vGlow;',
      'void main(){',
      '  vec4 tex = texture2D(uMap, gl_PointCoord);',
      '  if(tex.a < 0.02) discard;',
      '  float tw = pow(0.5 + 0.5 * sin(uTime * (0.55 + fract(vSeed) * 0.35) + vSeed), 4.0);',
      '  vec3 col = mix(uColorA, uColorB, smoothstep(0.12, 0.92, vLane) * 0.45 + tw * 0.42 + vGlow * 0.26);',
      '  float alpha = tex.a * uOpacity * (0.20 + vGlow * 0.78 + tw * 0.32 + uBeat * 0.10);',
      '  gl_FragColor = vec4(col * (0.82 + vGlow * 0.72 + tw * 0.32), alpha);',
      '}'
    ].join('\n'),
    transparent: true,
    depthWrite: false,
    depthTest: false,
    blending: THREE.AdditiveBlending
  });
  // 创建星河 Points，并放在歌词稍后的局部空间。
  var points = new THREE.Points(geo, mat);
  points.renderOrder = 45;
  points.frustumCulled = false;
  points.position.set(0, 0.20, 1.53);
  stageLyrics.group.add(points);
  stageLyrics.starRiver = points;
  return points;
}

// 每帧更新歌词星河的尺寸、透明度、色彩和轻微漂移。
function updateLyricStarRiver(dt) {
  // 确保星河对象存在。
  var river = ensureLyricStarRiver();
  // 材质异常时跳过。
  if (!river || !river.material || !river.material.uniforms) return;
  if (fx && fx.preset === SKULL_PRESET_INDEX) {
    // 骷髅预设的嘴部歌词不显示星河，避免干扰面部构图。
    river.visible = false;
    if (river.material.uniforms.uOpacity) river.material.uniforms.uOpacity.value = 0;
    return;
  }
  // 缓存 uniform 引用。
  var u = river.material.uniforms;
  // 当前歌词 mesh 上保存了文本世界尺寸。
  var data = stageLyrics.current && stageLyrics.current.userData ? stageLyrics.current.userData.lyric : null;
  // 星河宽度随歌词宽度变化。
  var targetW = data ? clampRange((data.textWorldW || data.worldW || 4.2) * 1.12 + 0.80, 2.25, 7.20) : 3.4;
  // 星河高度随歌词高度变化。
  var targetH = data ? clampRange((data.textWorldH || data.worldH || 0.58) * 1.85 + 0.18, 0.52, 1.35) : 0.58;
  stageLyrics.starRiverWidth += (targetW - stageLyrics.starRiverWidth) * Math.min(1, dt * 5.2);
  stageLyrics.starRiverHeight += (targetH - stageLyrics.starRiverHeight) * Math.min(1, dt * 4.6);
  u.uWidth.value = stageLyrics.starRiverWidth;
  u.uHeight.value = stageLyrics.starRiverHeight;
  // 歌词辉光开关和强度共同决定星河透明度。
  var lyricGlowStrength = fx.lyricGlow ? Math.min(0.85, Math.max(0, fx.lyricGlowStrength)) : 0;
  var targetOpacity = (stageLyrics.current && fx.lyricGlowParticles)
    ? clampRange(0.22 + lyricGlowStrength * 0.58 + stageLyrics.highBloom * 0.16 + stageLyrics.beatGlow * 0.12, 0.16, 0.86)
    : 0;
  u.uOpacity.value += (targetOpacity - u.uOpacity.value) * (targetOpacity > u.uOpacity.value ? 0.10 : 0.055);
  u.uColorA.value.copy(lyricThreeColor(stageLyrics.palette.secondary || stageLyrics.palette.primary, '#9cffdf', 0.42));
  u.uColorB.value.copy(lyricThreeColor(stageLyrics.palette.highlight || stageLyrics.palette.primary, '#fff7d2', 0.46));
  // 透明度接近 0 且无当前歌词时才隐藏对象。
  river.visible = u.uOpacity.value > 0.01 || !!stageLyrics.current;
  // 星河本体保持微弱漂浮，增强舞台层次。
  var t = uniforms.uTime.value;
  river.position.y += ((0.18 + Math.sin(t * 0.44) * 0.035 + Math.sin(t * 0.91 + 1.7) * 0.018) - river.position.y) * 0.08;
  river.position.z += ((1.54 + Math.cos(t * 0.31) * 0.060) - river.position.z) * 0.08;
  river.rotation.z = Math.sin(t * 0.22) * 0.012;
}

// 移除并释放单个歌词 mesh 及其所有子对象资源。
function disposeLyricMesh(mesh) {
  // 空对象直接跳过。
  if (!mesh) return;
  // 先从父级移除，避免继续参与渲染。
  if (mesh.parent) mesh.parent.remove(mesh);
  mesh.traverse(function(obj){
    if (obj.material) {
      // 多材质对象逐个释放贴图和材质。
      if (Array.isArray(obj.material)) {
        obj.material.forEach(function(m){ if (m.map) m.map.dispose(); m.dispose(); });
      } else {
        // 单材质对象需要处理普通 map 和自定义 uniform 贴图。
        if (obj.material.map) obj.material.map.dispose();
        if (obj.material.uniforms && obj.material.uniforms.uMap && obj.material.uniforms.uMap.value) obj.material.uniforms.uMap.value.dispose();
        obj.material.dispose();
      }
    }
    if (obj.geometry) obj.geometry.dispose();
  });
}

// 将数值限制在 0..1。
function clamp01(v) { return Math.max(0, Math.min(1, v)); }
// RGB 转 HSL，供歌词色板推导使用。
function rgbToHsl(r, g, b) {
  // 转换到 0..1 区间。
  r /= 255; g /= 255; b /= 255;
  // 取最大最小通道用于计算亮度、饱和度和色相。
  var max = Math.max(r, g, b), min = Math.min(r, g, b);
  // 默认灰度色的色相和饱和度为 0。
  var h = 0, s = 0, l = (max + min) / 2;
  if (max !== min) {
    // d 是通道跨度，决定饱和度。
    var d = max - min;
    s = l > 0.5 ? d / (2 - max - min) : d / (max + min);
    if (max === r) h = (g - b) / d + (g < b ? 6 : 0);
    else if (max === g) h = (b - r) / d + 2;
    else h = (r - g) / d + 4;
    h /= 6;
  }
  return { h:h, s:s, l:l };
}
// HSL 转 RGB，供色板调整后回写 CSS 色值。
function hslToRgb(h, s, l) {
  // 根据色相分段计算单个 RGB 通道。
  function hue2rgb(p, q, t) {
    if (t < 0) t += 1;
    if (t > 1) t -= 1;
    if (t < 1/6) return p + (q - p) * 6 * t;
    if (t < 1/2) return q;
    if (t < 2/3) return p + (q - p) * (2/3 - t) * 6;
    return p;
  }
  // 输出通道临时变量。
  var r, g, b;
  if (s === 0) r = g = b = l;
  else {
    // q/p 是 HSL 到 RGB 的标准中间参数。
    var q = l < 0.5 ? l * (1 + s) : l + s - l * s;
    var p = 2 * l - q;
    r = hue2rgb(p, q, h + 1/3);
    g = hue2rgb(p, q, h);
    b = hue2rgb(p, q, h - 1/3);
  }
  return { r:Math.round(r * 255), g:Math.round(g * 255), b:Math.round(b * 255) };
}
// 把 RGB 对象转成 CSS rgb/rgba 字符串。
function rgbCss(c, a) {
  if (a == null) return 'rgb(' + c.r + ',' + c.g + ',' + c.b + ')';
  return 'rgba(' + c.r + ',' + c.g + ',' + c.b + ',' + a + ')';
}
// 通用范围限制函数。
function clampRange(v, min, max) { return Math.max(min, Math.min(max, v)); }
// 归一化封面粒子分辨率档位。
function normalizeCoverResolution(v) {
  return clampRange(Number(v) || 1, 0.75, 1.55);
}
// 归一化后台性能策略。
function normalizePerformanceBackgroundMode(v, liveKeepFallback) {
  // 配置统一转为字符串再判断。
  var value = String(v || '');
  if (value === 'keep' || liveKeepFallback === true) return 'keep';
  if (value === 'release') return 'release';
  return 'auto';
}
// 归一化渲染质量档位。
function normalizePerformanceQuality(v) {
  // 只接受已知档位，非法值回退默认。
  var value = String(v || '');
  return /^(eco|balanced|high|ultra)$/.test(value) ? value : fxDefaults.performanceQuality;
}
// 根据分辨率档位计算封面粒子网格边长。
function coverParticleGridForResolution(v) {
  // 基准网格 118，按档位缩放。
  var grid = Math.round(118 * normalizeCoverResolution(v));
  // 限制网格边长，避免粒子数量过低或过高。
  grid = Math.max(88, Math.min(183, grid));
  // 保持奇数边长，让平面中心落在一个粒子上。
  return grid % 2 ? grid : grid + 1;
}
// 生成分辨率 UI 显示用的粒子网格标签。
function coverParticleCountLabel(v) {
  // 读取实际网格边长。
  var grid = coverParticleGridForResolution(v);
  return grid + 'x' + grid;
}
// 根据粒子分辨率选择封面纹理处理尺寸。
function coverTextureSizeForResolution(v) {
  // 先归一化档位，再映射到固定纹理尺寸。
  v = normalizeCoverResolution(v);
  if (v >= 1.32) return 512;
  if (v >= 1.10) return 384;
  return 256;
}
// 从 localStorage 读取歌词布局和视觉配置。
function readSavedLyricLayout() {
  try {
    // 读取原始 JSON 字符串。
    var savedLayoutRaw = localStorage.getItem(LYRIC_LAYOUT_STORE_KEY);
    // 没有用户保存时使用打包默认布局。
    var raw = savedLayoutRaw ? (JSON.parse(savedLayoutRaw) || {}) : packagedDefaultLyricLayoutRaw();
    // 读取并归一化视觉预设。
    var savedPreset = normalizeVisualPresetIndex(raw.preset, DEFAULT_PLAYBACK_VISUAL_PRESET);
    if (savedPreset === 3 && raw.visualPresetSchema !== VISUAL_PRESET_SCHEMA) {
      savedPreset = 5;
    }
    // 背景色和透明度按当前合法范围归一化。
    var savedBgColor = normalizeHexColor(raw.backgroundColor || '#000000', '#000000');
    var savedBgOpacity = clampRange(raw.backgroundOpacity == null ? fxDefaults.backgroundOpacity : Number(raw.backgroundOpacity), 0, 1);
    // 控制玻璃色散偏移需要限制在 UI 支持范围内。
    var savedGlassOffset = clampRange(raw.controlGlassChromaticOffset == null ? fxDefaults.controlGlassChromaticOffset : Number(raw.controlGlassChromaticOffset), 0, 140);
    // 背景颜色模式只接受封面或自定义。
    var savedBgMode = /^(cover|custom)$/.test(String(raw.backgroundColorMode || '')) ? String(raw.backgroundColorMode) : '';
    // 兼容旧字段 backgroundColorCustom 和透明度设置。
    var savedBgCustom = savedBgMode
      ? savedBgMode === 'custom'
      : (raw.backgroundColorCustom === true || (raw.backgroundColorCustom !== false && savedBgColor !== '#000000') || savedBgOpacity < 1);
    // 歌单架相机模式会影响默认角度。
    var savedShelfCameraMode = normalizeShelfCameraMode(raw.shelfCameraMode || fxDefaults.shelfCameraMode);
    // 手动角度标记用于判断是否覆盖默认角度。
    var savedShelfAngleManual = raw.shelfAngleYManual === true;
    // 最终歌单架角度，手动时读保存值，否则按模式取默认。
    var savedShelfAngle = savedShelfAngleManual
      ? clampRange(raw.shelfAngleY == null ? shelfDefaultAngleForCameraMode(savedShelfCameraMode) : Number(raw.shelfAngleY), -30, 30)
      : shelfDefaultAngleForCameraMode(savedShelfCameraMode);
    return {
      preset: savedPreset,
      intensity: clampRange(Number(raw.intensity) || fxDefaults.intensity, 0.2, 1.6),
      cinemaShake: clampRange(Number(raw.cinemaShake) || fxDefaults.cinemaShake, 0, 1.8),
      depth: clampRange(Number(raw.depth) || fxDefaults.depth, 0.2, 1.8),
      point: clampRange(Number(raw.point) || fxDefaults.point, 0.5, 2.2),
      speed: clampRange(Number(raw.speed) || fxDefaults.speed, 0.2, 2.5),
      twist: clampRange(Number(raw.twist) || fxDefaults.twist, 0, 0.6),
      color: clampRange(Number(raw.color) || fxDefaults.color, 0.5, 2.0),
      scatter: clampRange(Number(raw.scatter) || fxDefaults.scatter, 0, 0.5),
      bgFade: clampRange(Number(raw.bgFade) || fxDefaults.bgFade, 0, 1.2),
      bloomStrength: clampRange(Number(raw.bloomStrength) || fxDefaults.bloomStrength, 0, 1.6),
      lyricGlowStrength: clampRange(Number(raw.lyricGlowStrength) || fxDefaults.lyricGlowStrength, 0, 0.85),
      lyricScale: clampRange(Number(raw.lyricScale) || 1, 0.35, 1.65),
      lyricOffsetX: clampRange(Number(raw.lyricOffsetX) || 0, -2.0, 2.0),
      lyricOffsetY: clampRange(Number(raw.lyricOffsetY) || 0, -1.2, 1.35),
      lyricOffsetZ: clampRange(Number(raw.lyricOffsetZ) || 0, -1.6, 1.6),
      lyricTiltX: clampRange(Number(raw.lyricTiltX) || 0, -42, 42),
      lyricTiltY: clampRange(Number(raw.lyricTiltY) || 0, -42, 42),
      lyricCameraLock: !!raw.lyricCameraLock,
      lyricColorMode: raw.lyricColorMode === 'custom' ? 'custom' : 'auto',
      lyricColor: normalizeHexColor(raw.lyricColor || '#a9b8c8'),
      lyricHighlightMode: raw.lyricHighlightMode === 'custom' ? 'custom' : 'auto',
      lyricHighlightColor: normalizeHexColor(raw.lyricHighlightColor || '#fff0b8'),
      lyricGlowLinked: raw.lyricGlowLinked !== false,
      lyricGlowColor: normalizeHexColor(raw.lyricGlowColor || '#9db8cf'),
      lyricFont: normalizeLyricFontKey(raw.lyricFont),
      lyricLetterSpacing: clampRange(Number(raw.lyricLetterSpacing) || 0, -0.04, 0.18),
      lyricLineHeight: clampRange(Number(raw.lyricLineHeight) || 1, 0.86, 1.35),
      lyricWeight: clampRange(Number(raw.lyricWeight) || 900, 500, 900),
      lyricGlow: raw.lyricGlow !== false,
      lyricGlowBeat: raw.lyricGlowBeat !== false,
      lyricGlowParticles: !!raw.lyricGlowParticles,
      cinema: raw.cinema !== false,
      bloom: raw.bloom === true,
      edge: raw.edge === true,
      aiDepth: !!raw.aiDepth,
      visualTintMode: raw.visualTintMode === 'custom' ? 'custom' : 'auto',
      visualTintColor: normalizeHexColor(raw.visualTintColor || '#9db8cf'),
      uiAccentColor: normalizeHexColor(raw.uiAccentColor || '#00f5d4', '#00f5d4'),
      visualIconColor: normalizeHexColor(raw.visualIconColor || fxDefaults.visualIconColor || '#7fd8ff', '#7fd8ff'),
      backgroundColorMode: savedBgCustom ? 'custom' : 'cover',
      backgroundColor: savedBgColor,
      backgroundOpacity: savedBgOpacity,
      controlGlassChromaticOffset: savedGlassOffset,
      backgroundColorCustom: savedBgCustom,
      backgroundImage: normalizeCustomBackgroundImage(raw.backgroundImage),
      backgroundMedia: normalizeCustomBackgroundMedia(raw.backgroundMedia || raw.backgroundImage),
      performanceBackground: normalizePerformanceBackgroundMode(raw.performanceBackground, raw.liveBackgroundKeep === true),
      performanceQuality: normalizePerformanceQuality(raw.performanceQuality),
      liveBackgroundKeep: normalizePerformanceBackgroundMode(raw.performanceBackground, raw.liveBackgroundKeep === true) === 'keep',
      wallpaperMode: false,
      wallpaperOpacity: clampRange(raw.wallpaperOpacity == null ? fxDefaults.wallpaperOpacity : Number(raw.wallpaperOpacity), 0.35, 1),
      coverResolution: normalizeCoverResolution(raw.coverResolution),
      shelf: /^(off|side|stage)$/.test(String(raw.shelf || '')) ? raw.shelf : fxDefaults.shelf,
      shelfCameraMode: savedShelfCameraMode,
      shelfPresence: normalizeShelfPresence(raw.shelfPresence || fxDefaults.shelfPresence),
      shelfSize: clampRange(raw.shelfSize == null ? fxDefaults.shelfSize : Number(raw.shelfSize), 0.65, 1.45),
      shelfOffsetX: clampRange(raw.shelfOffsetX == null ? fxDefaults.shelfOffsetX : Number(raw.shelfOffsetX), -1.2, 1.2),
      shelfOffsetY: clampRange(raw.shelfOffsetY == null ? fxDefaults.shelfOffsetY : Number(raw.shelfOffsetY), -0.9, 0.9),
      shelfOffsetZ: clampRange(raw.shelfOffsetZ == null ? fxDefaults.shelfOffsetZ : Number(raw.shelfOffsetZ), -0.9, 0.9),
      shelfAngleY: savedShelfAngle,
      shelfAngleYManual: savedShelfAngleManual,
      shelfOpacity: clampRange(raw.shelfOpacity == null ? fxDefaults.shelfOpacity : Number(raw.shelfOpacity), 0.25, 1),
      shelfBgOpacity: clampRange(raw.shelfBgOpacity == null ? fxDefaults.shelfBgOpacity : Number(raw.shelfBgOpacity), 0.25, 0.98),
      shelfAccentColor: normalizeHexColor(raw.shelfAccentColor || fxDefaults.shelfAccentColor, fxDefaults.shelfAccentColor)
    };
  } catch (e) {
    // 读取失败时返回空对象，由调用方使用默认配置兜底。
    return {};
  }
}
// 保存当前歌词布局和视觉配置到 localStorage。
function saveLyricLayout() {
  try {
    // 保存前再次归一化预设索引，避免写入非法值。
    var presetForSave = normalizeVisualPresetIndex(fx.preset, DEFAULT_PLAYBACK_VISUAL_PRESET);
    localStorage.setItem(LYRIC_LAYOUT_STORE_KEY, JSON.stringify({
      visualPresetSchema: VISUAL_PRESET_SCHEMA,
      preset: presetForSave,
      intensity: clampRange(Number(fx.intensity) || fxDefaults.intensity, 0.2, 1.6),
      cinemaShake: clampRange(Number(fx.cinemaShake) || fxDefaults.cinemaShake, 0, 1.8),
      depth: clampRange(Number(fx.depth) || fxDefaults.depth, 0.2, 1.8),
      point: clampRange(Number(fx.point) || fxDefaults.point, 0.5, 2.2),
      speed: clampRange(Number(fx.speed) || fxDefaults.speed, 0.2, 2.5),
      twist: clampRange(Number(fx.twist) || fxDefaults.twist, 0, 0.6),
      color: clampRange(Number(fx.color) || fxDefaults.color, 0.5, 2.0),
      scatter: clampRange(Number(fx.scatter) || fxDefaults.scatter, 0, 0.5),
      bgFade: clampRange(Number(fx.bgFade) || fxDefaults.bgFade, 0, 1.2),
      bloomStrength: clampRange(Number(fx.bloomStrength) || fxDefaults.bloomStrength, 0, 1.6),
      lyricGlowStrength: clampRange(Number(fx.lyricGlowStrength) || fxDefaults.lyricGlowStrength, 0, 0.85),
      lyricScale: clampRange(Number(fx.lyricScale) || 1, 0.35, 1.65),
      lyricOffsetX: clampRange(Number(fx.lyricOffsetX) || 0, -2.0, 2.0),
      lyricOffsetY: clampRange(Number(fx.lyricOffsetY) || 0, -1.2, 1.35),
      lyricOffsetZ: clampRange(Number(fx.lyricOffsetZ) || 0, -1.6, 1.6),
      lyricTiltX: clampRange(Number(fx.lyricTiltX) || 0, -42, 42),
      lyricTiltY: clampRange(Number(fx.lyricTiltY) || 0, -42, 42),
      lyricCameraLock: !!fx.lyricCameraLock,
      lyricColorMode: fx.lyricColorMode === 'custom' ? 'custom' : 'auto',
      lyricColor: normalizeHexColor(fx.lyricColor || '#a9b8c8'),
      lyricHighlightMode: fx.lyricHighlightMode === 'custom' ? 'custom' : 'auto',
      lyricHighlightColor: normalizeHexColor(fx.lyricHighlightColor || '#fff0b8'),
      lyricGlowLinked: fx.lyricGlowLinked !== false,
      lyricGlowColor: normalizeHexColor(fx.lyricGlowColor || '#9db8cf'),
      lyricFont: normalizeLyricFontKey(fx.lyricFont),
      lyricLetterSpacing: clampRange(Number(fx.lyricLetterSpacing) || 0, -0.04, 0.18),
      lyricLineHeight: clampRange(Number(fx.lyricLineHeight) || 1, 0.86, 1.35),
      lyricWeight: clampRange(Number(fx.lyricWeight) || 900, 500, 900),
      lyricGlow: !!fx.lyricGlow,
      lyricGlowBeat: !!fx.lyricGlowBeat,
      lyricGlowParticles: !!fx.lyricGlowParticles,
      cinema: !!fx.cinema,
      bloom: !!fx.bloom,
      edge: !!fx.edge,
      aiDepth: !!fx.aiDepth,
      visualTintMode: fx.visualTintMode === 'custom' ? 'custom' : 'auto',
      visualTintColor: normalizeHexColor(fx.visualTintColor || '#9db8cf'),
      uiAccentColor: normalizeHexColor(fx.uiAccentColor || '#00f5d4', '#00f5d4'),
      visualIconColor: normalizeHexColor(fx.visualIconColor || '#7fd8ff', '#7fd8ff'),
      backgroundColorMode: fx.backgroundColorMode === 'custom' || fx.backgroundColorCustom ? 'custom' : 'cover',
      backgroundColor: normalizeHexColor(fx.backgroundColor || '#000000', '#000000'),
      backgroundOpacity: clampRange(fx.backgroundOpacity == null ? fxDefaults.backgroundOpacity : Number(fx.backgroundOpacity), 0, 1),
      controlGlassChromaticOffset: clampRange(fx.controlGlassChromaticOffset == null ? fxDefaults.controlGlassChromaticOffset : Number(fx.controlGlassChromaticOffset), 0, 140),
      backgroundColorCustom: fx.backgroundColorMode === 'custom' || !!fx.backgroundColorCustom,
      backgroundImage: normalizeCustomBackgroundImage(fx.backgroundImage),
      backgroundMedia: normalizeCustomBackgroundMedia(fx.backgroundMedia || fx.backgroundImage),
      performanceBackground: normalizePerformanceBackgroundMode(fx.performanceBackground, fx.liveBackgroundKeep === true),
      performanceQuality: normalizePerformanceQuality(fx.performanceQuality),
      liveBackgroundKeep: normalizePerformanceBackgroundMode(fx.performanceBackground, fx.liveBackgroundKeep === true) === 'keep',
      wallpaperMode: false,
      wallpaperOpacity: clampRange(fx.wallpaperOpacity == null ? fxDefaults.wallpaperOpacity : Number(fx.wallpaperOpacity), 0.35, 1),
      coverResolution: normalizeCoverResolution(fx.coverResolution),
      shelf: /^(off|side|stage)$/.test(String(fx.shelf || '')) ? fx.shelf : fxDefaults.shelf,
      shelfCameraMode: normalizeShelfCameraMode(fx.shelfCameraMode || fxDefaults.shelfCameraMode),
      shelfPresence: normalizeShelfPresence(fx.shelfPresence || fxDefaults.shelfPresence),
      shelfSize: clampRange(fx.shelfSize == null ? fxDefaults.shelfSize : Number(fx.shelfSize), 0.65, 1.45),
      shelfOffsetX: clampRange(fx.shelfOffsetX == null ? fxDefaults.shelfOffsetX : Number(fx.shelfOffsetX), -1.2, 1.2),
      shelfOffsetY: clampRange(fx.shelfOffsetY == null ? fxDefaults.shelfOffsetY : Number(fx.shelfOffsetY), -0.9, 0.9),
      shelfOffsetZ: clampRange(fx.shelfOffsetZ == null ? fxDefaults.shelfOffsetZ : Number(fx.shelfOffsetZ), -0.9, 0.9),
      shelfAngleY: clampRange(fx.shelfAngleY == null ? fxDefaults.shelfAngleY : Number(fx.shelfAngleY), -30, 30),
      shelfAngleYManual: fx.shelfAngleYManual === true,
      shelfOpacity: clampRange(fx.shelfOpacity == null ? fxDefaults.shelfOpacity : Number(fx.shelfOpacity), 0.25, 1),
      shelfBgOpacity: clampRange(fx.shelfBgOpacity == null ? fxDefaults.shelfBgOpacity : Number(fx.shelfBgOpacity), 0.25, 0.98),
      shelfAccentColor: normalizeHexColor(fx.shelfAccentColor || fxDefaults.shelfAccentColor, fxDefaults.shelfAccentColor)
    }));
  } catch (e) {}
}
// 归一化十六进制颜色，支持 #rgb 展开。
function normalizeHexColor(value, fallback) {
  // 先把输入转为去空格字符串。
  var hex = String(value || '').trim();
  if (/^#[0-9a-f]{3}$/i.test(hex)) {
    // 三位十六进制展开为六位。
    hex = '#' + hex.charAt(1) + hex.charAt(1) + hex.charAt(2) + hex.charAt(2) + hex.charAt(3) + hex.charAt(3);
  }
  // fallback 本身也必须是合法六位色，否则使用歌词默认色。
  fallback = /^#[0-9a-f]{6}$/i.test(String(fallback || '')) ? String(fallback).toLowerCase() : '#a9b8c8';
  return /^#[0-9a-f]{6}$/i.test(hex) ? hex.toLowerCase() : fallback;
}
// 归一化歌单架相机模式。
function normalizeShelfCameraMode(value) {
  return String(value || '') === 'static' ? 'static' : 'dynamic';
}
// 根据歌单架相机模式给出默认 Y 轴角度。
function shelfDefaultAngleForCameraMode(mode) {
  return normalizeShelfCameraMode(mode) === 'static' ? -15 : 0;
}
// 按当前相机模式应用歌单架默认角度。
function applyShelfCameraDefaultAngle(force) {
  // fx 尚未初始化时不处理。
  if (!fx) return;
  // 先确保相机模式合法。
  fx.shelfCameraMode = normalizeShelfCameraMode(fx.shelfCameraMode || fxDefaults.shelfCameraMode);
  if (force || fx.shelfAngleYManual !== true) {
    // 强制或未手动设置时，使用模式默认角度。
    fx.shelfAngleYManual = false;
    fx.shelfAngleY = shelfDefaultAngleForCameraMode(fx.shelfCameraMode);
  } else {
    // 手动角度只做范围裁剪和整数化。
    fx.shelfAngleY = Math.round(clampRange(Number(fx.shelfAngleY) || 0, -30, 30));
  }
}
// 归一化歌单架存在策略。
function normalizeShelfPresence(value) {
  return String(value || '') === 'always' ? 'always' : 'auto';
}
// 读取并裁剪歌单架数字设置。
function normalizedShelfNumber(key, fallback, min, max) {
  // 优先读取 fx 中的当前值。
  var value = fx && fx[key] != null ? Number(fx[key]) : fallback;
  // 非数值回退默认。
  if (!isFinite(value)) value = fallback;
  return clampRange(value, min, max);
}
// 汇总歌单架当前布局设置。
function shelfSettings() {
  // 角度可能来自手动设置，也可能由相机模式默认决定。
  var angleDeg = fx && fx.shelfAngleYManual === true
    ? normalizedShelfNumber('shelfAngleY', shelfDefaultAngleForCameraMode(fx.shelfCameraMode), -30, 30)
    : shelfDefaultAngleForCameraMode(fx && fx.shelfCameraMode);
  return {
    size: normalizedShelfNumber('shelfSize', fxDefaults.shelfSize, 0.65, 1.45),
    x: normalizedShelfNumber('shelfOffsetX', fxDefaults.shelfOffsetX, -1.2, 1.2),
    y: normalizedShelfNumber('shelfOffsetY', fxDefaults.shelfOffsetY, -0.9, 0.9),
    z: normalizedShelfNumber('shelfOffsetZ', fxDefaults.shelfOffsetZ, -0.9, 0.9),
    angle: angleDeg * Math.PI / 180,
    opacity: normalizedShelfNumber('shelfOpacity', fxDefaults.shelfOpacity, 0.25, 1),
    bgOpacity: normalizedShelfNumber('shelfBgOpacity', fxDefaults.shelfBgOpacity, 0.25, 0.98),
    accent: normalizeHexColor((fx && fx.shelfAccentColor) || fxDefaults.shelfAccentColor, fxDefaults.shelfAccentColor)
  };
}
// 判断歌单架是否配置为始终可见。
function shelfAlwaysVisible() {
  return !!(fx && normalizeShelfPresence(fx.shelfPresence) === 'always');
}
// 判断当前歌单架相关相机类型是否使用动态相机。
function shouldUseShelfDynamicCamera(type) {
  // 非歌单架相机类型默认允许动态处理。
  if (!/^shelf-/.test(String(type || ''))) return true;
  // 静态模式下禁用歌单架动态相机。
  return !(fx && normalizeShelfCameraMode(fx.shelfCameraMode) === 'static');
}
// 读取当前歌单架强调色。
function shelfAccentHex() {
  return normalizeHexColor((fx && fx.shelfAccentColor) || fxDefaults.shelfAccentColor, fxDefaults.shelfAccentColor);
}
// 把歌单架强调色转换为 rgba 字符串。
function shelfAccentRgba(alpha, fallback) {
  // 先转为 RGB 对象。
  var rgb = hexToRgb(shelfAccentHex());
  // 转换失败时使用传入兜底或默认暖色。
  if (!rgb) return fallback || 'rgba(244,210,138,' + alpha + ')';
  return 'rgba(' + rgb.r + ',' + rgb.g + ',' + rgb.b + ',' + alpha + ')';
}
// 将 RGB 数值转换为六位十六进制颜色。
function rgbToHexColor(r, g, b) {
  // 单通道转换并裁剪到 0..255。
  function part(v) {
    return Math.max(0, Math.min(255, Math.round(v || 0))).toString(16).padStart(2, '0');
  }
  return '#' + part(r) + part(g) + part(b);
}
// 归一化歌词字体配置键。
function normalizeLyricFontKey(value) {
  // 未配置时默认使用 sans。
  value = String(value || 'sans');
  return /^(sans|hei|song|bold-song|stone-song|kai-song|serif-en|gothic|editorial|humanist|round|mono|display)$/.test(value) ? value : 'sans';
}
// 根据字体配置键返回 canvas 可用的字体栈。
function lyricFontStackForKey(key) {
  // 先归一化，确保后续分支只处理合法键。
  key = normalizeLyricFontKey(key);
  if (key === 'hei') return '"Noto Sans SC","Microsoft YaHei",SimHei,"PingFang SC",sans-serif';
  if (key === 'song') return '"Noto Serif SC","Source Han Serif SC",SimSun,"Songti SC",serif';
  if (key === 'bold-song') return '"Source Han Serif SC Heavy","Source Han Serif SC","Noto Serif SC Black","Noto Serif SC","STZhongsong","SimSun",serif';
  if (key === 'stone-song') return '"FZYaSongS-B-GB","FZCuSong-B09S","Source Han Serif SC Heavy","Noto Serif SC Black","STZhongsong","SimSun",serif';
  if (key === 'kai-song') return '"Kaiti SC","STKaiti","KaiTi","Source Han Serif SC","Noto Serif SC",serif';
  if (key === 'serif-en') return 'Georgia,"Times New Roman","Noto Serif SC","Source Han Serif SC",serif';
  if (key === 'gothic') return '"UnifrakturCook","UnifrakturMaguntia","Old English Text MT","Blackletter","Cinzel Decorative","Noto Serif SC",serif';
  if (key === 'editorial') return '"Didot","Bodoni 72","Libre Baskerville",Georgia,"Noto Serif SC",serif';
  if (key === 'humanist') return '"Avenir Next","Segoe UI","Inter","Noto Sans SC","PingFang SC",sans-serif';
  if (key === 'round') return '"HarmonyOS Sans SC","Microsoft YaHei UI","PingFang SC","Noto Sans SC",sans-serif';
  if (key === 'mono') return '"JetBrains Mono",Consolas,"Noto Sans SC","Microsoft YaHei",monospace';
  if (key === 'display') return '"Alibaba PuHuiTi","Noto Sans SC","PingFang SC","Microsoft YaHei",sans-serif';
  return 'Inter,"Noto Sans SC","PingFang SC","Microsoft YaHei",Arial,sans-serif';
}
// 读取歌词字体字重。
function lyricFontWeightValue() {
  // 石刻宋体风格强制使用最高字重，保证纹理效果厚重。
  if (normalizeLyricFontKey(fx && fx.lyricFont) === 'stone-song') return 900;
  return Math.round(clampRange(Number(fx && fx.lyricWeight) || 900, 500, 900) / 50) * 50;
}
// 生成 canvas 字体 CSS 字符串。
function lyricFontCss(fontSize) {
  return lyricFontWeightValue() + ' ' + fontSize + 'px ' + lyricFontStackForKey(fx && fx.lyricFont);
}
// 根据字体大小计算歌词字距像素值。
function lyricLetterSpacingPx(fontSize) {
  return clampRange(Number(fx && fx.lyricLetterSpacing) || 0, -0.04, 0.18) * Math.max(1, fontSize || 1);
}
// 读取歌词行高倍率。
function lyricLineHeightFactor() {
  return clampRange(Number(fx && fx.lyricLineHeight) || 1, 0.86, 1.35);
}
// 测量带自定义字距的文本宽度。
function measureTextWithLetterSpacing(ctx, text, spacing) {
  // 保证输入是字符串。
  text = String(text || '');
  // 字距非法时按 0 处理。
  spacing = Number(spacing) || 0;
  // 没有字距或单字符时直接使用 canvas 原生测量。
  if (!spacing || text.length < 2) return ctx.measureText(text).width;
  // Array.from 能正确处理代理对和部分组合字符。
  var chars = Array.from(text);
  // 累加后的文本宽度。
  var w = 0;
  for (var i = 0; i < chars.length; i++) {
    w += ctx.measureText(chars[i]).width;
    if (i < chars.length - 1) w += spacing;
  }
  return Math.max(1, w);
}
// 按当前歌词配置测量文本宽度。
function lyricMeasureText(ctx, text, fontSize) {
  return measureTextWithLetterSpacing(ctx, text, lyricLetterSpacingPx(fontSize));
}
// 绘制带自定义字距的文本，支持填充和描边。
function drawTextWithLetterSpacing(ctx, text, x, y, spacing, stroke) {
  // 统一输入格式。
  text = String(text || '');
  spacing = Number(spacing) || 0;
  if (!spacing || text.length < 2) {
    // 没有字距时保留 canvas 原生对齐行为。
    if (stroke) ctx.strokeText(text, x, y);
    else ctx.fillText(text, x, y);
    return;
  }
  // 拆成可迭代字符，避免普通 split 拆坏 emoji 或扩展字符。
  var chars = Array.from(text);
  // 记录原始对齐方式，绘制后恢复。
  var align = ctx.textAlign || 'left';
  // 按自定义字距测量总宽。
  var width = measureTextWithLetterSpacing(ctx, text, spacing);
  // 根据原始对齐方式计算左侧起点。
  var start = x;
  if (align === 'center') start = x - width / 2;
  else if (align === 'right' || align === 'end') start = x - width;
  ctx.textAlign = 'left';
  // 当前字符绘制位置。
  var cursor = start;
  for (var i = 0; i < chars.length; i++) {
    if (stroke) ctx.strokeText(chars[i], cursor, y);
    else ctx.fillText(chars[i], cursor, y);
    cursor += ctx.measureText(chars[i]).width + (i < chars.length - 1 ? spacing : 0);
  }
  ctx.textAlign = align;
}
// 使用当前字距配置绘制填充歌词文本。
function lyricFillText(ctx, text, x, y, fontSize) {
  drawTextWithLetterSpacing(ctx, text, x, y, lyricLetterSpacingPx(fontSize), false);
}
// 使用当前字距配置绘制描边歌词文本。
function lyricStrokeText(ctx, text, x, y, fontSize) {
  drawTextWithLetterSpacing(ctx, text, x, y, lyricLetterSpacingPx(fontSize), true);
}
// 给石刻宋体歌词叠加颗粒、刮痕和缺口质感。
function applyStonePrintTexture(ctx, W, H, fontSize) {
  // 只有 stone-song 字体风格启用这层纹理。
  if (normalizeLyricFontKey(fx && fx.lyricFont) !== 'stone-song') return;
  // 纹理尺度随字体大小变化并限制范围。
  var size = clampRange(fontSize || 128, 42, 180);
  // 只在文字主体所在的中间带区域打磨纹理。
  var bandTop = H * 0.10;
  var bandH = H * 0.80;
  ctx.save();
  // destination-out 会从已经绘制的文字中扣出纹理。
  ctx.globalCompositeOperation = 'destination-out';

  // 生成一张小噪声贴图，再拉伸覆盖文字区域。
  var noiseW = 300, noiseH = 110;
  var noise = document.createElement('canvas');
  noise.width = noiseW; noise.height = noiseH;
  // 噪声 canvas 的上下文。
  var nctx = noise.getContext('2d');
  // 噪声像素数据。
  var img = nctx.createImageData(noiseW, noiseH);
  for (var p = 0; p < noiseW * noiseH; p++) {
    // 像素坐标用于生成带方向感的纹理纹路。
    var x0 = p % noiseW;
    var y0 = Math.floor(p / noiseW);
    // vein 叠加低频条纹，避免纯随机噪声过脏。
    var vein = Math.sin(x0 * 0.19 + y0 * 0.043) * 0.10 + Math.sin(y0 * 0.31) * 0.06;
    // r 决定当前像素的剥落透明度。
    var r = Math.random() + vein;
    // a 是用于抠除文字的 alpha。
    var a = 0;
    if (r > 0.82) a = 78 + Math.random() * 92;
    else if (r > 0.62) a = 22 + Math.random() * 54;
    else if (r > 0.48) a = 4 + Math.random() * 24;
    img.data[p * 4] = 255;
    img.data[p * 4 + 1] = 255;
    img.data[p * 4 + 2] = 255;
    img.data[p * 4 + 3] = a;
  }
  nctx.putImageData(img, 0, 0);
  ctx.imageSmoothingEnabled = false;
  ctx.globalAlpha = 0.34;
  ctx.drawImage(noise, 0, bandTop, W, bandH);

  // 随机矩形缺口模拟石印掉墨。
  var chips = Math.round(size * 7.2);
  for (var i = 0; i < chips; i++) {
    // 单个缺口的位置和尺寸。
    var x = Math.random() * W;
    var y = bandTop + Math.random() * bandH;
    var w = 0.7 + Math.random() * (size * 0.052);
    var h = 0.45 + Math.random() * (size * 0.026);
    ctx.globalAlpha = 0.16 + Math.random() * 0.36;
    ctx.save();
    ctx.translate(x, y);
    ctx.rotate((Math.random() - 0.5) * 0.38);
    ctx.fillRect(-w / 2, -h / 2, w, h);
    ctx.restore();
  }

  // 细线刮痕增强旧印刷质感。
  ctx.lineCap = 'round';
  for (var s = 0; s < 44; s++) {
    // 单条刮痕的起点。
    var sx = Math.random() * W;
    var sy = bandTop + Math.random() * bandH;
    ctx.globalAlpha = 0.09 + Math.random() * 0.16;
    ctx.lineWidth = 0.45 + Math.random() * 1.2;
    ctx.beginPath();
    ctx.moveTo(sx, sy);
    ctx.lineTo(sx + 10 + Math.random() * 86, sy + (Math.random() - 0.5) * 4.8);
    ctx.stroke();
  }

  // 椭圆磨损块用于模拟局部色块脱落。
  for (var c = 0; c < 26; c++) {
    // 单个磨损块中心和半径。
    var cx = Math.random() * W;
    var cy = bandTop + Math.random() * bandH;
    var radius = 1.8 + Math.random() * (size * 0.060);
    ctx.globalAlpha = 0.08 + Math.random() * 0.18;
    ctx.beginPath();
    ctx.ellipse(cx, cy, radius * (0.7 + Math.random() * 1.4), radius * (0.25 + Math.random() * 0.55), Math.random() * Math.PI, 0, Math.PI * 2);
    ctx.fill();
  }
  ctx.restore();
}
// 将六位十六进制颜色转换为 RGB 对象。
function hexToRgb(hex) {
  // normalizeHexColor 保证后续 slice 可用。
  hex = normalizeHexColor(hex).slice(1);
  return {
    r: parseInt(hex.slice(0, 2), 16),
    g: parseInt(hex.slice(2, 4), 16),
    b: parseInt(hex.slice(4, 6), 16)
  };
}
// 归一化自定义背景图片来源。
function normalizeCustomBackgroundImage(value) {
  // 仅接受 data URL 图片或 http(s) 地址。
  var src = String(value || '').trim();
  if (!src) return '';
  if (/^data:image\/(png|jpe?g|webp);base64,/i.test(src)) return src;
  if (/^https?:\/\//i.test(src)) return src;
  return '';
}
// 归一化自定义背景媒体，兼容旧字符串字段和新对象字段。
function normalizeCustomBackgroundMedia(value) {
  // 空值表示没有自定义媒体。
  if (!value) return null;
  if (typeof value === 'string') {
    // 字符串先尝试作为图片处理。
    var img = normalizeCustomBackgroundImage(value);
    if (img) return { type: 'image', src: img };
    if (/^data:video\/(mp4|webm|quicktime);base64,/i.test(value) || /^https?:\/\//i.test(value)) return { type: 'video', src: String(value) };
    return null;
  }
  // 非对象无法表达媒体元数据。
  if (typeof value !== 'object') return null;
  // 只接受图片和视频两类。
  var type = value.type === 'video' ? 'video' : (value.type === 'image' ? 'image' : '');
  if (type === 'image') {
    // 图片对象同样只保留合法来源。
    var imageSrc = normalizeCustomBackgroundImage(value.src || value.url || '');
    return imageSrc ? { type: 'image', src: imageSrc } : null;
  }
  if (type === 'video') {
    // 视频可以通过 IndexedDB id 或 data/http(s) src 引用。
    var src = String(value.src || '').trim();
    // IndexedDB 中保存的视频对象 ID。
    var id = String(value.id || '').trim();
    if (!id && !/^data:video\/(mp4|webm|quicktime);base64,/i.test(src) && !/^https?:\/\//i.test(src)) return null;
    return {
      type: 'video',
      id: id,
      src: src,
      name: String(value.name || '').slice(0, 120),
      mime: String(value.mime || '').slice(0, 80),
      size: Math.max(0, Number(value.size) || 0)
    };
  }
  return null;
}
// 返回自定义背景媒体在 UI 上的简短状态文本。
function customBackgroundMediaLabel(media) {
  // 先归一化，避免展示无效媒体。
  media = normalizeCustomBackgroundMedia(media);
  if (!media) return '未设置';
  return media.type === 'video' ? '视频已设置' : '图片已设置';
}
// 自定义背景 IndexedDB 数据库名。
var CUSTOM_BG_DB_NAME = 'mineradio-custom-background-v1';
// 自定义背景 IndexedDB 对象仓库名。
var CUSTOM_BG_STORE = 'media';
// 当前自定义背景对象 URL，替换媒体时需要回收。
var customBgObjectUrl = '';
// 自定义背景应用 token，用于异步加载防串。
var customBgApplyToken = 0;
// 打开自定义背景 IndexedDB。
function openCustomBackgroundDb() {
  return new Promise(function(resolve, reject){
    // 浏览器不支持 IndexedDB 时直接拒绝。
    if (!window.indexedDB) { reject(new Error('indexedDB unavailable')); return; }
    // 当前数据库版本为 1。
    var req = indexedDB.open(CUSTOM_BG_DB_NAME, 1);
    req.onupgradeneeded = function(){
      // 首次创建数据库时建立 media 仓库。
      var db = req.result;
      if (!db.objectStoreNames.contains(CUSTOM_BG_STORE)) db.createObjectStore(CUSTOM_BG_STORE, { keyPath: 'id' });
    };
    req.onsuccess = function(){ resolve(req.result); };
    req.onerror = function(){ reject(req.error || new Error('indexedDB open failed')); };
  });
}
// 将自定义背景 Blob 写入 IndexedDB。
async function putCustomBackgroundBlob(id, blob, meta) {
  // 先打开数据库连接。
  var db = await openCustomBackgroundDb();
  return new Promise(function(resolve, reject){
    // 写入需要 readwrite 事务。
    var tx = db.transaction(CUSTOM_BG_STORE, 'readwrite');
    tx.objectStore(CUSTOM_BG_STORE).put(Object.assign({ id: id, blob: blob, savedAt: Date.now() }, meta || {}));
    tx.oncomplete = function(){ db.close(); resolve(); };
    tx.onerror = function(){ db.close(); reject(tx.error || new Error('indexedDB put failed')); };
  });
}
// 根据 id 从 IndexedDB 读取自定义背景 Blob。
async function getCustomBackgroundBlob(id) {
  // 先打开数据库连接。
  var db = await openCustomBackgroundDb();
  return new Promise(function(resolve, reject){
    // 读取使用 readonly 事务。
    var tx = db.transaction(CUSTOM_BG_STORE, 'readonly');
    // 获取指定媒体记录。
    var req = tx.objectStore(CUSTOM_BG_STORE).get(id);
    req.onsuccess = function(){ resolve(req.result && req.result.blob ? req.result.blob : null); };
    req.onerror = function(){ reject(req.error || new Error('indexedDB get failed')); };
    tx.oncomplete = function(){ db.close(); };
  });
}
// 封面深度缓存 IndexedDB 配置。
var DEPTH_DB_NAME = 'echo-player-depths';
var DEPTH_STORE = 'depths';
// 打开深度缓存 IndexedDB。
function openDepthDB() {
  return new Promise(function(resolve, reject){
    if (!window.indexedDB) { reject(new Error('indexedDB unavailable')); return; }
    var req = indexedDB.open(DEPTH_DB_NAME, 1);
    req.onupgradeneeded = function(){
      var db = req.result;
      if (!db.objectStoreNames.contains(DEPTH_STORE)) db.createObjectStore(DEPTH_STORE, { keyPath: 'hash' });
    };
    req.onsuccess = function(){ resolve(req.result); };
    req.onerror = function(){ reject(req.error || new Error('indexedDB open failed')); };
  });
}
// 从 IndexedDB 读取指定 hash 的深度缓存。
async function getDepthFromIDB(hash) {
  if (!hash) return null;
  try {
    var db = await openDepthDB();
    return new Promise(function(resolve, reject){
      var tx = db.transaction(DEPTH_STORE, 'readonly');
      var req = tx.objectStore(DEPTH_STORE).get(hash);
      req.onsuccess = function(){ resolve(req.result || null); };
      req.onerror = function(){ reject(req.error); };
      tx.oncomplete = function(){ db.close(); };
    });
  } catch (e) {
    console.warn('[深度缓存] IDB 读取失败', e);
    return null;
  }
}
// 将深度缓存写入 IndexedDB（所有写入均为 AI 深度，标记 ai: true）。
async function putDepthToIDB(hash, dataUrl, width, height) {
  if (!hash || !dataUrl) return;
  try {
    var db = await openDepthDB();
    return new Promise(function(resolve, reject){
      var tx = db.transaction(DEPTH_STORE, 'readwrite');
      tx.objectStore(DEPTH_STORE).put({ hash: hash, dataUrl: dataUrl, width: width, height: height, ai: true, timestamp: Date.now() });
      tx.oncomplete = function(){ db.close(); resolve(); };
      tx.onerror = function(){ db.close(); reject(tx.error); };
    });
  } catch (e) {
    console.warn('[深度缓存] IDB 写入失败', e);
  }
}
// 颜色实验室弹层的运行状态。
var colorLabState = { picker: null, id: '', h: 0, s: 1, v: 1, dragging: false };
// 颜色实验室内置预设色。
var COLOR_LAB_PRESETS = [
  { name: '极黑', color: '#000000' },
  { name: '极白', color: '#ffffff' },
  { name: '克莱因蓝', color: '#002fa7' },
  { name: '法拉利红', color: '#f00000' },
  { name: '香槟金', color: '#c8a96a' },
  { name: '孔雀绿', color: '#006b5b' },
  { name: '午夜紫', color: '#2b164f' },
  { name: '银雾', color: '#d9dde2' }
];
// RGB 转 HSV，供颜色实验室二维面板使用。
function rgbToHsv(r, g, b) {
  // 转换到 0..1 区间。
  r /= 255; g /= 255; b /= 255;
  // 取最大最小通道计算色相、饱和度和明度。
  var max = Math.max(r, g, b), min = Math.min(r, g, b);
  // d 是通道跨度，灰度色时色相保持 0。
  var d = max - min, h = 0;
  if (d) {
    if (max === r) h = ((g - b) / d + (g < b ? 6 : 0)) / 6;
    else if (max === g) h = ((b - r) / d + 2) / 6;
    else h = ((r - g) / d + 4) / 6;
  }
  return { h: h, s: max === 0 ? 0 : d / max, v: max };
}
// HSV 转十六进制颜色。
function hsvToHex(h, s, v) {
  // 色相循环，饱和度和明度裁剪。
  h = ((h % 1) + 1) % 1; s = clampRange(s, 0, 1); v = clampRange(v, 0, 1);
  // HSV 六分区参数。
  var i = Math.floor(h * 6), f = h * 6 - i;
  // 中间颜色通道。
  var p = v * (1 - s), q = v * (1 - f * s), t = v * (1 - (1 - f) * s);
  // 输出 RGB 通道。
  var r, g, b;
  switch (i % 6) {
    case 0: r = v; g = t; b = p; break;
    case 1: r = q; g = v; b = p; break;
    case 2: r = p; g = v; b = t; break;
    case 3: r = p; g = q; b = v; break;
    case 4: r = t; g = p; b = v; break;
    default: r = v; g = p; b = q; break;
  }
  return rgbToHexColor(r * 255, g * 255, b * 255);
}
// 将颜色实验室当前值应用到对应的设置项。
function applyColorLabValue(hex, silent) {
  // 统一成合法颜色。
  hex = normalizeHexColor(hex || '#000000', '#000000');
  // 当前弹层绑定的控件 id 决定写入哪个设置。
  var id = colorLabState.id;
  if (id === 'ui-accent-picker') setUiAccentColor(hex, true);
  else if (id === 'visual-tint-picker') setVisualTintCustom(hex, true);
  else if (id === 'visual-icon-picker') setVisualIconColor(hex, true);
  else if (id === 'bg-color-picker') setCustomBackgroundColor(hex, true, true);
  else if (id === 'shelf-accent-picker') setShelfAccentColor(hex, true);
  else if (id === 'lyric-color-picker') setLyricColorCustom(hex, true);
  else if (id === 'lyric-highlight-picker') setLyricHighlightCustom(hex, true);
  else if (id === 'lyric-glow-picker') setLyricGlowCustom(hex, true);
  if (!silent) showToast('颜色: ' + hex.toUpperCase());
}
// 根据十六进制颜色同步颜色实验室 UI 状态。
function syncColorLabUi(hex) {
  // 统一输入颜色。
  hex = normalizeHexColor(hex || '#000000', '#000000');
  // 转换为 HSV，驱动色相条和饱和明度面板。
  var rgb = hexToRgb(hex);
  var hsv = rgbToHsv(rgb.r, rgb.g, rgb.b);
  colorLabState.h = hsv.h; colorLabState.s = hsv.s; colorLabState.v = hsv.v;
  // 查找弹层和控件节点。
  var pop = document.getElementById('color-lab-pop');
  var sv = document.getElementById('color-lab-sv');
  var cursor = document.getElementById('color-lab-cursor');
  var hue = document.getElementById('color-lab-hue');
  var hexInput = document.getElementById('color-lab-hex');
  var preview = document.getElementById('color-lab-preview');
  // 当前色相对应的纯色，用于面板背景。
  var hueHex = hsvToHex(colorLabState.h, 1, 1);
  if (pop) {
    pop.style.setProperty('--lab-color', hex);
    pop.style.setProperty('--lab-hue', hueHex);
  }
  if (sv) sv.style.setProperty('--lab-hue', hueHex);
  if (cursor) { cursor.style.left = (colorLabState.s * 100).toFixed(2) + '%'; cursor.style.top = ((1 - colorLabState.v) * 100).toFixed(2) + '%'; }
  if (hue) hue.value = Math.round(colorLabState.h * 360);
  if (hexInput) hexInput.value = hex.toUpperCase();
  if (preview) preview.style.setProperty('--lab-color', hex);
}
// 关闭颜色实验室弹层并清理绑定状态。
function closeColorLab() {
  // 隐藏弹层 DOM。
  var pop = document.getElementById('color-lab-pop');
  if (pop) pop.classList.remove('show');
  // 解除当前 picker 绑定。
  colorLabState.picker = null;
  colorLabState.id = '';
}
// 把视觉控制台的浮动面板放到锚点附近，并限制在视口内。
function placeFxFloatingPanel(pop, anchor, opts) {
  // 必须有面板和可测量的锚点。
  if (!pop || !anchor || !anchor.getBoundingClientRect) return;
  // opts 控制间距和视口边距。
  opts = opts || {};
  // 面板与锚点之间的间隔。
  var gap = opts.gap == null ? 12 : opts.gap;
  // 面板与视口边缘的最小留白。
  var pad = opts.pad == null ? 14 : opts.pad;
  // 锚点矩形。
  var rect = anchor.getBoundingClientRect();
  // 视口宽高兜底到 320，避免极端环境出现负尺寸。
  var vw = Math.max(320, window.innerWidth || document.documentElement.clientWidth || 320);
  var vh = Math.max(320, window.innerHeight || document.documentElement.clientHeight || 320);
  // 面板实际尺寸，同时不能超过视口安全宽高。
  var pw = Math.min(pop.offsetWidth || pop.getBoundingClientRect().width || 330, vw - pad * 2);
  var ph = Math.min(pop.offsetHeight || pop.getBoundingClientRect().height || 260, vh - pad * 2);
  // 最终左上角位置。
  var left;
  var top;
  if (vw < 760) {
    left = Math.max(pad, Math.min(vw - pw - pad, rect.left + rect.width / 2 - pw / 2));
    top = rect.bottom + gap;
    if (top + ph > vh - pad) top = Math.max(pad, rect.top - ph - gap);
  } else {
    var roomRight = vw - rect.right - pad;
    var roomLeft = rect.left - pad;
    if (roomRight >= pw + gap || roomRight >= roomLeft) left = rect.right + gap;
    else left = rect.left - pw - gap;
    left = Math.max(pad, Math.min(vw - pw - pad, left));
    top = rect.top + rect.height / 2 - ph / 2;
    top = Math.max(pad, Math.min(vh - ph - pad, top));
  }
  pop.style.left = Math.round(left) + 'px';
  pop.style.top = Math.round(top) + 'px';
  pop.style.transform = 'none';
}
// 打开颜色实验室并绑定到指定颜色选择器。
function openColorLabForPicker(picker) {
  // 查找颜色实验室弹层。
  var pop = document.getElementById('color-lab-pop');
  // 没有选择器或弹层时不能打开。
  if (!picker || !pop) return;
  if (pop.classList.contains('show') && colorLabState.picker === picker) {
    // 再次点击同一个选择器时关闭弹层。
    closeColorLab();
    return;
  }
  // 记录当前绑定的 picker 和 id。
  colorLabState.picker = picker;
  colorLabState.id = picker.id || '';
  // 颜色行用于定位弹层和生成标题。
  var label = picker.closest('.lyric-color-row');
  // 弹层标题显示当前颜色项名称。
  var title = document.getElementById('color-lab-title');
  if (title) title.textContent = label ? (label.textContent || 'Color').replace(/#[0-9a-f]{6}/ig, '').trim().slice(0, 24) : 'Color';
  // 用 picker 当前值同步 HSV 面板。
  syncColorLabUi(picker.value || '#000000');
  // 渲染预设色按钮。
  var presets = document.getElementById('color-lab-presets');
  if (presets) {
    presets.innerHTML = COLOR_LAB_PRESETS.map(function(p){
      return '<button type="button" title="' + escHtml(p.name) + '" style="--c:' + p.color + '" data-color="' + p.color + '"></button>';
    }).join('');
  }
  // 显示弹层并放到对应颜色行附近。
  pop.classList.add('show');
  placeFxFloatingPanel(pop, label || picker, { gap: 12, pad: 14 });
}
// 根据饱和度/明度面板上的指针位置更新颜色。
function updateColorLabFromSv(e) {
  // 查找二维颜色区域。
  var sv = document.getElementById('color-lab-sv');
  if (!sv) return;
  // 读取区域尺寸，将指针坐标转换成 0..1。
  var rect = sv.getBoundingClientRect();
  colorLabState.s = clampRange((e.clientX - rect.left) / Math.max(1, rect.width), 0, 1);
  colorLabState.v = 1 - clampRange((e.clientY - rect.top) / Math.max(1, rect.height), 0, 1);
  // 根据当前 HSV 得到新颜色。
  var hex = hsvToHex(colorLabState.h, colorLabState.s, colorLabState.v);
  // 同步 UI 并静默写入目标设置。
  syncColorLabUi(hex);
  applyColorLabValue(hex, true);
}
// 给原生颜色 input 绑定自定义颜色实验室交互。
function bindColorLabPicker(picker) {
  // 避免重复绑定同一个 input。
  if (!picker || picker._colorLabBound) return;
  picker._colorLabBound = true;
  // 标记此控件会打开 dialog 样式弹层。
  picker.setAttribute('aria-haspopup', 'dialog');
  picker.setAttribute('data-color-lab-picker', '1');
  // 从 pointer/click/键盘事件统一打开弹层。
  function openFromPickerEvent(e) {
    if (e) {
      // 阻止原生颜色选择器弹出，改用自定义颜色实验室。
      e.preventDefault();
      e.stopPropagation();
    }
    picker._colorLabOpenedAt = Date.now();
    openColorLabForPicker(picker);
  }
  picker.addEventListener('pointerdown', openFromPickerEvent);
  // mousedown/click 都阻止原生颜色选择器抢焦点。
  picker.addEventListener('mousedown', function(e){ e.preventDefault(); e.stopPropagation(); });
  picker.addEventListener('click', function(e){
    e.preventDefault();
    e.stopPropagation();
    if (Date.now() - (picker._colorLabOpenedAt || 0) < 260) return;
    openColorLabForPicker(picker);
  });
  picker.addEventListener('keydown', function(e){
    // 键盘也支持回车和空格打开。
    if (e.key === 'Enter' || e.key === ' ') openFromPickerEvent(e);
  });
}
// 把浮动弹层节点提升到 body，避免被控制台容器裁剪。
function liftFxFloatingPopups() {
  ['cover-color-pop', 'color-lab-pop', 'cover-color-loupe'].forEach(function(id){
    // 只移动已存在且不在 body 下的节点。
    var el = document.getElementById(id);
    if (el && el.parentElement !== document.body) document.body.appendChild(el);
  });
}
// 给颜色行绑定点击打开颜色实验室的交互。
function bindColorLabRows() {
  document.querySelectorAll('.lyric-color-row').forEach(function(row){
    // 已绑定、无效或联动行不处理。
    if (!row || row._colorLabRowBound || row.classList.contains('linked')) return;
    // 行内必须有颜色选择器。
    var picker = row.querySelector('.lyric-color-picker');
    if (!picker) return;
    row._colorLabRowBound = true;
    row.addEventListener('pointerdown', function(e){
      // 忽略按钮、滑杆、选择框等子控件事件。
      if (!e || !e.target) return;
      if (e.target.closest('button,.fx-mini-btn,input[type="range"],select,textarea')) return;
      e.preventDefault();
      e.stopPropagation();
      picker._colorLabOpenedAt = Date.now();
      openColorLabForPicker(picker);
    });
  });
}
// 视口变化或布局变化时重新定位已打开的浮动面板。
function repositionFxFloatingPanels() {
  // 颜色实验室跟随当前 picker。
  var colorPop = document.getElementById('color-lab-pop');
  if (colorPop && colorPop.classList.contains('show') && colorLabState.picker) {
    placeFxFloatingPanel(colorPop, colorLabState.picker.closest('.lyric-color-row') || colorLabState.picker, { gap: 12, pad: 14 });
  }
  // 封面取色弹层跟随视觉色调自动按钮或 picker。
  var coverPop = document.getElementById('cover-color-pop');
  if (coverPop && coverPop.classList.contains('show')) {
    placeFxFloatingPanel(coverPop, document.getElementById('visual-tint-auto-btn') || document.getElementById('visual-tint-picker') || coverPop, { gap: 12, pad: 14 });
  }
}
// 窗口尺寸变化时重排浮动面板。
window.addEventListener('resize', function(){
  if (window.requestAnimationFrame) requestAnimationFrame(repositionFxFloatingPanels);
  else repositionFxFloatingPanels();
});
// 读取当前 UI 强调色。
function uiAccentHex(fallback) {
  return normalizeHexColor((fx && fx.uiAccentColor) || fallback || '#00f5d4', fallback || '#00f5d4');
}
// 把 UI 强调色转换为 rgba 字符串。
function uiAccentRgba(alpha, fallback) {
  // 先把强调色转换成 RGB。
  var c = hexToRgb(uiAccentHex(fallback));
  return 'rgba(' + c.r + ',' + c.g + ',' + c.b + ',' + (alpha == null ? 1 : alpha) + ')';
}
// 根据背景色亮度选择可读的前景墨色。
function readableInkForHex(hex) {
  // 计算感知亮度。
  var c = hexToRgb(hex || '#00f5d4');
  var lum = (c.r * 0.299 + c.g * 0.587 + c.b * 0.114) / 255;
  return lum > 0.54 ? '#06100f' : '#f8fbff';
}
// 从一个十六进制颜色生成歌词色板。
function lyricPaletteFromHex(hex) {
  // 转换为 RGB 和 HSL，便于调整亮度和饱和度。
  var c = hexToRgb(hex);
  var hsl = rgbToHsl(c.r, c.g, c.b);
  // 低饱和色按中性处理，避免强行生成有色副色。
  var neutral = hsl.s < 0.035;
  // 计算适合歌词主色的饱和度。
  var s = neutral ? 0 : clampRange(hsl.s * 1.08, 0.14, 0.92);
  // 根据输入亮度调整到歌词可读范围。
  var l = hsl.l;
  if (l < 0.11) l = 0.15 + l * 1.18;
  else if (l < 0.28) l = 0.21 + (l - 0.11) * 1.18;
  else l = clampRange(l, 0.30, 0.82);
  l = clampRange(l, 0.14, 0.84);
  // 主色、副色和高亮色分别从同一色相附近派生。
  var primary = hslToRgb(hsl.h, s, l);
  var secondary = hslToRgb((hsl.h + 0.055) % 1, neutral ? 0 : clampRange(s * 0.88, 0.12, 0.78), clampRange(l + (l < 0.38 ? 0.10 : -0.08), 0.18, 0.76));
  var highlight = hslToRgb((hsl.h + 0.018) % 1, neutral ? 0 : clampRange(s * 0.72, 0.10, 0.70), clampRange(l + 0.22, 0.38, 0.92));
  // 深色歌词用深阴影，浅色歌词用浅阴影。
  var darkText = l < 0.40;
  return {
    primary: rgbCss(primary),
    secondary: rgbCss(secondary),
    highlight: rgbCss(highlight),
    shadow: darkText ? 'rgba(0,6,10,0.46)' : 'rgba(248,253,255,0.34)',
    glow: rgbCss(primary, 0.26),
  };
}
// 封面过暗或低彩度时使用的银蓝默认歌词色板。
function silverBlueLyricPalette() {
  return {
    primary: '#d8f1ff',
    secondary: '#9db8cf',
    highlight: '#eef7ff',
    shadow: 'rgba(0,7,12,0.48)',
    glow: 'rgba(138,190,255,0.26)',
  };
}
// 设置歌词粒子火花透明度，兼容 ShaderMaterial 和普通 PointsMaterial。
function setLyricSparkOpacity(data, value) {
  // 没有火花材质时跳过。
  if (!data || !data.sparkMat) return;
  // 裁剪透明度范围。
  value = clampRange(Number(value) || 0, 0, 1);
  if (data.sparkMat.uniforms && data.sparkMat.uniforms.uOpacity) data.sparkMat.uniforms.uOpacity.value = value;
  else data.sparkMat.opacity = value;
}
// 读取歌词粒子火花透明度。
function getLyricSparkOpacity(data) {
  // 缺省透明度为 0。
  if (!data || !data.sparkMat) return 0;
  if (data.sparkMat.uniforms && data.sparkMat.uniforms.uOpacity) return Number(data.sparkMat.uniforms.uOpacity.value) || 0;
  return Number(data.sparkMat.opacity) || 0;
}
// 设置歌词粒子火花尺寸。
function setLyricSparkSize(data, value) {
  // 没有火花材质时跳过。
  if (!data || !data.sparkMat) return;
  // 保证粒子尺寸有最小值。
  value = Math.max(0.002, Number(value) || 0.035);
  if (data.sparkMat.uniforms && data.sparkMat.uniforms.uSize) data.sparkMat.uniforms.uSize.value = value;
  else data.sparkMat.size = value;
}
// 读取歌词粒子火花尺寸。
function getLyricSparkSize(data) {
  // 缺省尺寸和创建时保持一致。
  if (!data || !data.sparkMat) return 0.035;
  if (data.sparkMat.uniforms && data.sparkMat.uniforms.uSize) return Number(data.sparkMat.uniforms.uSize.value) || 0.035;
  return Number(data.sparkMat.size) || 0.035;
}
// 设置歌词火花颜色，兼容 shader uniform 和普通材质 color。
function setLyricSparkColor(data, color) {
  // 没有火花材质时跳过。
  if (!data || !data.sparkMat) return;
  if (data.sparkMat.uniforms && data.sparkMat.uniforms.uColor) data.sparkMat.uniforms.uColor.value.copy(color);
  else if (data.sparkMat.color) data.sparkMat.color.copy(color);
}
// 将当前歌词色板应用到已存在的歌词 mesh。
function applyLyricPaletteToMesh(mesh) {
  // mesh 没有歌词数据时跳过。
  if (!mesh || !mesh.userData || !mesh.userData.lyric) return;
  // 当前有效歌词色板。
  var pal = stageLyrics.palette || {};
  // 歌词 mesh 的材质和子层数据。
  var data = mesh.userData.lyric;
  if (data.textMat && data.textMat.uniforms) {
    // 更新文字 shader 的基础色、高亮色、辉光色和暖光色。
    var u = data.textMat.uniforms;
    if (u.uBaseColor) u.uBaseColor.value.copy(lyricThreeColor(pal.primary, '#d6f8ff', 0.38));
    if (u.uHiColor) u.uHiColor.value.copy(lyricThreeColor(pal.highlight || pal.primary, '#fff0b8', 0.48));
    if (u.uGlowColor) u.uGlowColor.value.copy(lyricThreeColor(pal.glowColor || pal.secondary || pal.primary, '#9cffdf', 0.36));
    if (u.uSolarColor) u.uSolarColor.value.copy(lyricThreeColor(pal.highlight || pal.secondary || pal.primary, '#fff0b8', 0.50));
    if (u.uSolar && !isFinite(u.uSolar.value)) u.uSolar.value = 0;
    if (u.uOpacity && !isFinite(u.uOpacity.value)) u.uOpacity.value = 0;
    data.textMat.needsUpdate = true;
  }
  if (data.glowMat) data.glowMat.color.copy(lyricThreeColor(pal.glowColor || pal.secondary || pal.primary, '#9cffdf', 0.36));
  if (data.sparkMat) setLyricSparkColor(data, lyricThreeColor(pal.highlight || pal.secondary || pal.primary, '#fff0b8', 0.46));
  if (data.sunMat) data.sunMat.color.copy(lyricThreeColor(pal.highlight || pal.secondary || pal.primary, '#fff0b8', 0.50));
}
// 合并封面色板和用户自定义歌词色设置，得到最终歌词色板。
function effectiveLyricPalette(pal) {
  // 输入色板优先，其次封面色板，最后当前色板。
  var src = pal || stageLyrics.coverPalette || stageLyrics.palette || {};
  // 先生成基础输出，确保字段齐全。
  var out = {
    primary: src.primary || '#d6f8ff',
    secondary: src.secondary || '#9cffdf',
    highlight: src.highlight || '#eef7ff',
    shadow: src.shadow || 'rgba(2,8,12,0.42)',
    glow: src.glow || 'rgba(143,233,255,0.34)'
  };
  if (fx.lyricHighlightMode === 'custom') {
    // 自定义高亮色只替换高亮，必要时联动辉光色。
    var hi = lyricPaletteFromHex(fx.lyricHighlightColor);
    out.highlight = hi.primary;
    if (fx.lyricGlowLinked !== false) {
      out.glowColor = hi.secondary || hi.primary;
      out.glow = hi.glow || out.glow;
    }
  }
  if (fx.lyricGlowLinked === false) {
    // 关闭联动时，辉光使用独立自定义颜色。
    var glowPal = lyricPaletteFromHex(fx.lyricGlowColor || '#9db8cf');
    out.glowColor = glowPal.primary;
    out.glow = glowPal.glow || out.glow;
  }
  if (!out.glowColor) out.glowColor = out.secondary;
  return out;
}
// 设置舞台歌词色板并同步所有相关对象。
function setStageLyricPalette(pal) {
  // 先计算最终有效色板。
  stageLyrics.palette = effectiveLyricPalette(pal);
  // 更新歌词暖光缓存色。
  lyricSunColor.copy(lyricThreeColor(stageLyrics.palette.glowColor || stageLyrics.palette.secondary || stageLyrics.palette.primary, '#ffe6a4', 0.44));
  lyricSunHotColor.copy(lyricThreeColor(stageLyrics.palette.highlight || stageLyrics.palette.primary, '#fff4cc', 0.54));
  applyLyricPaletteToMesh(stageLyrics.current);
  stageLyrics.outgoing.forEach(applyLyricPaletteToMesh);
  syncSkullParticleColors();
}
// 根据封面主色的 HSL、平均亮度和彩度生成歌词色板。
function lyricTextPaletteFromHsl(hsl, avgL, chroma) {
  if (avgL < 0.16 || chroma < 0.08) {
    // 过暗或低彩度封面使用银蓝色，保证可读性。
    return silverBlueLyricPalette();
  }
  // 取封面代表色相。
  var hue = hsl.h;
  if (avgL < 0.30 && (hue < 0.06 || hue > 0.86 || (hue > 0.75 && hue < 0.86))) return silverBlueLyricPalette();
  if (avgL > 0.82 && chroma < 0.12) {
    // 很亮且低彩度的封面使用偏深的青色文字。
    return {
      primary: '#064b5b',
      secondary: '#168c88',
      highlight: '#315f68',
      shadow: 'rgba(255,255,255,0.48)',
      glow: 'rgba(143,233,255,0.14)',
    };
  }
  // 暗封面用亮字，亮封面用深字。
  var lightText = avgL < 0.52;
  // 提高饱和度，让歌词比封面更醒目。
  var s = Math.max(0.42, Math.min(0.78, hsl.s + 0.16));
  // 主色和副色。
  var c1 = hslToRgb(hsl.h, s, lightText ? 0.74 : 0.34);
  var c2 = hslToRgb((hsl.h + 0.08) % 1, Math.max(0.36, s - 0.10), lightText ? 0.62 : 0.46);
  return {
    primary: rgbCss(c1),
    secondary: rgbCss(c2),
    highlight: rgbCss(hslToRgb((hsl.h + 0.03) % 1, Math.max(0.28, s - 0.18), lightText ? 0.86 : 0.58)),
    shadow: lightText ? 'rgba(0,6,10,0.44)' : 'rgba(248,253,255,0.40)',
    glow: rgbCss(c1, lightText ? 0.24 : 0.14),
  };
}
// 从封面 canvas 抽样更新歌词自动色板。
function updateLyricPaletteFromCover(coverCanvas) {
  // 没有封面 canvas 时保持现有色板。
  if (!coverCanvas) return;
  try {
    // 读取封面像素数据。
    var ctx = coverCanvas.getContext('2d');
    var img = ctx.getImageData(0, 0, coverCanvas.width, coverCanvas.height).data;
    // 缓存宽高。
    var w = coverCanvas.width, h = coverCanvas.height;
    // 累加平均亮度所需的 RGB 和样本数。
    var sumR = 0, sumG = 0, sumB = 0, count = 0;
    // best 保存最适合做歌词色相参考的高彩度像素。
    var best = { score:-1, r:143, g:233, b:255 };
    for (var y = 0; y < h; y += 8) {
      for (var x = 0; x < w; x += 8) {
        var di = (y * w + x) * 4;
        // 当前采样点 RGBA。
        var r = img[di], g = img[di+1], b = img[di+2], a = img[di+3] / 255;
        if (a < 0.5) continue;
        // 亮度和彩度用于评分。
        var lum = (r * 0.299 + g * 0.587 + b * 0.114) / 255;
        var maxC = Math.max(r, g, b), minC = Math.min(r, g, b);
        var chroma = (maxC - minC) / 255;
        var edgePenalty = Math.abs(lum - 0.5);
        // 中等亮度且彩度高的像素更适合做歌词色。
        var score = chroma * 1.6 + (0.5 - edgePenalty) * 0.45;
        sumR += r; sumG += g; sumB += b; count++;
        if (lum > 0.08 && lum < 0.92 && score > best.score) best = { score:score, r:r, g:g, b:b };
      }
    }
    if (!count) return;
    // 计算封面平均亮度。
    var avgL = (sumR / count * 0.299 + sumG / count * 0.587 + sumB / count * 0.114) / 255;
    // 代表色转 HSL 后生成歌词色板。
    var hsl = rgbToHsl(best.r, best.g, best.b);
    stageLyrics.coverPalette = lyricTextPaletteFromHsl(hsl, avgL, Math.max(0, best.score));
    if (fx.lyricColorMode !== 'custom') setStageLyricPalette(stageLyrics.coverPalette);
  } catch (e) {}
}

// 将歌词文本按宽度和行数限制拆分成多行。
function wrapLyricText(ctx, text, maxWidth, maxLines, fontSize) {
  // 清理输入文本。
  text = String(text || '').trim();
  // 英文/数字带空格时按词组切，中文等无空格文本按字符切。
  var useWords = /\s/.test(text) && /[A-Za-z0-9]/.test(text);
  // 拆分单元，保留空格以便英文排版。
  var units = useWords ? text.split(/(\s+)/).filter(Boolean) : text.split('');
  // 输出行和当前行。
  var lines = [], line = '';
  for (var i = 0; i < units.length; i++) {
    // 尝试把当前单元加入当前行。
    var test = line + units[i];
    if (lyricMeasureText(ctx, test, fontSize) > maxWidth && line) {
      // 超宽时提交当前行，并从当前单元开启新行。
      lines.push(line.trim());
      line = units[i].trimStart ? units[i].trimStart() : units[i].replace(/^\s+/, '');
      if (lines.length >= maxLines) {
        // 超过最大行数时用省略号截断最后一行。
        var rest = units.slice(i).join('').trim();
        if (rest) lines[lines.length - 1] = lines[lines.length - 1].replace(/[.。,…，、\s]*$/, '') + '...';
        return lines;
      }
    } else {
      line = test;
    }
  }
  if (line && lines.length < maxLines) lines.push(line.trim());
  return lines.length ? lines : [''];
}

// 将 CSS 颜色字符串转换为 Three.Color。
function cssColorToThreeColor(css, fallback) {
  // 先用 fallback 初始化，解析失败时保持这个颜色。
  var c = new THREE.Color(fallback || '#d6f8ff');
  // 支持十六进制、rgb/rgba 和浏览器可识别的 CSS 色。
  var value = String(css || fallback || '#d6f8ff').trim();
  try {
    if (/^#[0-9a-f]{3}$/i.test(value) || /^#[0-9a-f]{6}$/i.test(value)) {
      c.set(normalizeHexColor(value));
      return c;
    }
    // 解析 rgb/rgba 数字格式。
    var m = value.match(/^rgba?\(\s*([.\d]+)\s*,\s*([.\d]+)\s*,\s*([.\d]+)/i);
    if (m) {
      c.setRGB(
        Math.max(0, Math.min(255, parseFloat(m[1]))) / 255,
        Math.max(0, Math.min(255, parseFloat(m[2]))) / 255,
        Math.max(0, Math.min(255, parseFloat(m[3]))) / 255
      );
      return c;
    }
    c.setStyle(value);
  } catch (e) {
    // setStyle 失败时再次尝试 fallback。
    try { c.set(normalizeHexColor(fallback || '#d6f8ff')); } catch (e2) {}
  }
  return c;
}
// 转换歌词用 Three.Color，并确保最低亮度。
function lyricThreeColor(css, fallback, minLum) {
  // 先解析 CSS 颜色。
  var c = cssColorToThreeColor(css, fallback || '#d6f8ff');
  // 感知亮度用于避免歌词过暗。
  var lum = c.r * 0.299 + c.g * 0.587 + c.b * 0.114;
  // floor 是最小亮度阈值。
  var floor = minLum == null ? 0.34 : minLum;
  if (lum < floor) {
    // 直接抬升 RGB 通道，保持色相大致不变。
    var lift = floor - lum;
    c.r = Math.min(1, c.r + lift);
    c.g = Math.min(1, c.g + lift);
    c.b = Math.min(1, c.b + lift);
  }
  return c;
}

// 舞台歌词最大行数，当前保持单行以适配 3D 舞台构图。
var STAGE_LYRIC_MAX_LINES = 1;

// 将歌词文本绘制成 alpha 遮罩贴图。
function makeLyricMask(text) {
  // 独立 canvas 用于绘制文字遮罩。
  var canvas = document.createElement('canvas');
  // 遮罩固定高分辨率，保证文字边缘细腻。
  var W = 2048, H = 384;
  canvas.width = W; canvas.height = H;
  // 绘制上下文。
  var ctx = canvas.getContext('2d');
  // 文字最大宽度，左右保留边距给辉光和抗锯齿。
  var maxWidth = W - 190;
  // 最大行数来自全局歌词配置。
  var maxLines = STAGE_LYRIC_MAX_LINES;
  // 初始字号，从大到小尝试适配。
  var fontSize = 128;
  // 归一化歌词文本空白。
  text = String(text || '').replace(/\s+/g, ' ').trim();
  // 当前适配后的行数组。
  var lines = [text];
  // 当前最宽行宽度。
  var widest = 1;
  for (; fontSize >= 42; fontSize -= 4) {
    // 设置当前尝试字号。
    ctx.font = lyricFontCss(fontSize);
    // 如果允许多行且超宽，按宽度换行。
    lines = maxLines > 1 && lyricMeasureText(ctx, text, fontSize) > maxWidth ? wrapLyricText(ctx, text, maxWidth, maxLines, fontSize) : [text];
    widest = 1;
    // 测量所有行，找到最宽行。
    for (var li = 0; li < lines.length; li++) widest = Math.max(widest, lyricMeasureText(ctx, lines[li], fontSize));
    if (widest <= maxWidth) break;
  }
  // 使用最终字号重新测量。
  ctx.font = lyricFontCss(fontSize);
  if (!lines.length) lines = [''];
  widest = 1;
  for (var mi = 0; mi < lines.length; mi++) widest = Math.max(widest, lyricMeasureText(ctx, lines[mi], fontSize));
  // 记录实际文字宽度。
  var width = Math.min(maxWidth, widest);
  // 单行仍超宽时做水平压缩，避免直接裁切文字。
  var fitScaleX = maxLines <= 1 && widest > maxWidth ? Math.max(0.68, maxWidth / widest) : 1;
  if (fitScaleX < 1) width = Math.min(maxWidth, widest * fitScaleX);
  // 行高与块高度用于绘制居中和世界尺寸换算。
  var lineHeight = fontSize * (lines.length > 1 ? 1.02 : 1.0) * lyricLineHeightFactor();
  var blockH = fontSize + (lines.length - 1) * lineHeight;
  // 绘制起点，整体垂直居中。
  var x = W / 2, y0 = H / 2 - blockH / 2 + fontSize * 0.82;
  ctx.clearRect(0, 0, W, H);
  ctx.textAlign = 'center';
  ctx.textBaseline = 'alphabetic';
  ctx.fillStyle = '#fff';
  for (var di = 0; di < lines.length; di++) {
    if (fitScaleX < 1) {
      // 水平压缩时以中心为原点缩放。
      ctx.save();
      ctx.translate(x, 0);
      ctx.scale(fitScaleX, 1);
      lyricFillText(ctx, lines[di], 0, y0 + di * lineHeight, fontSize);
      ctx.restore();
    } else {
      lyricFillText(ctx, lines[di], x, y0 + di * lineHeight, fontSize);
    }
  }
  // 石刻字体额外扣出印刷纹理。
  applyStonePrintTexture(ctx, W, H, fontSize);
  // 把遮罩 canvas 转为 Three.js 纹理。
  var tex = new THREE.CanvasTexture(canvas);
  tex.minFilter = THREE.LinearFilter;
  tex.magFilter = THREE.LinearFilter;
  tex.generateMipmaps = false;
  tex.anisotropy = Math.min(8, renderer.capabilities.getMaxAnisotropy ? renderer.capabilities.getMaxAnisotropy() : 1);
  // 返回纹理以及后续布局和 shader 需要的文本边界信息。
  return { texture:tex, width:W, height:H, textWidth:width, textHeight:blockH, fontSize:fontSize, lineHeight:lineHeight, lineCount:lines.length, lines:lines, fitScaleX:fitScaleX, textMin:(W / 2 - width / 2) / W, textMax:(W / 2 + width / 2) / W };
}

// 为歌词生成只跟随文字形状的黑白可读性描边贴图。
function makeLyricReadabilityTexture(mask) {
  // 可读性层与文字遮罩保持同尺寸。
  var canvas = document.createElement('canvas');
  // 读取遮罩尺寸和排版信息。
  var W = mask && mask.width || 2048;
  var H = mask && mask.height || 384;
  var fontSize = mask && mask.fontSize || 128;
  var lines = mask && Array.isArray(mask.lines) && mask.lines.length ? mask.lines : [''];
  var lineHeight = mask && mask.lineHeight || fontSize * lyricLineHeightFactor();
  var fitScaleX = mask && mask.fitScaleX || 1;
  canvas.width = W; canvas.height = H;
  // 绘制上下文。
  var ctx = canvas.getContext('2d');
  ctx.clearRect(0, 0, W, H);
  ctx.font = lyricFontCss(fontSize);
  ctx.textAlign = 'center';
  ctx.textBaseline = 'alphabetic';
  ctx.lineJoin = 'round';
  ctx.lineCap = 'round';
  ctx.miterLimit = 2;
  // 当前文本块高度和首行基线。
  var blockH = fontSize + (lines.length - 1) * lineHeight;
  var y0 = H / 2 - blockH / 2 + fontSize * 0.82;
  // 按指定偏移描边所有歌词行。
  function strokeLines(dx, dy) {
    for (var i = 0; i < lines.length; i++) {
      // 当前行基线。
      var y = y0 + i * lineHeight + (dy || 0);
      if (fitScaleX < 1) {
        // 与遮罩绘制一致，超宽歌词需要水平压缩。
        ctx.save();
        ctx.translate(W / 2 + (dx || 0), 0);
        ctx.scale(fitScaleX, 1);
        lyricStrokeText(ctx, lines[i], 0, y, fontSize);
        ctx.restore();
      } else {
        lyricStrokeText(ctx, lines[i], W / 2 + (dx || 0), y, fontSize);
      }
    }
  }

  // Black/white readability layer: text-shaped only, no rectangular backing.
  // 第一层大范围黑色柔影，用于浅色背景可读性。
  ctx.save();
  ctx.filter = 'blur(14px)';
  ctx.globalAlpha = 0.18;
  ctx.lineWidth = Math.max(18, fontSize * 0.16);
  ctx.strokeStyle = 'rgba(0,0,0,1)';
  strokeLines(0, fontSize * 0.018);
  ctx.restore();

  // 第二层较细黑描边，增强字形边界。
  ctx.save();
  ctx.filter = 'blur(5px)';
  ctx.globalAlpha = 0.32;
  ctx.lineWidth = Math.max(9, fontSize * 0.075);
  ctx.strokeStyle = 'rgba(0,0,0,1)';
  strokeLines(0, fontSize * 0.012);
  ctx.restore();

  // 第三层白色柔边，帮助深色背景上的字形分离。
  ctx.save();
  ctx.filter = 'blur(4px)';
  ctx.globalAlpha = 0.15;
  ctx.lineWidth = Math.max(9, fontSize * 0.070);
  ctx.strokeStyle = 'rgba(255,255,255,1)';
  strokeLines(0, 0);
  ctx.restore();

  // 第四层更细的白色边缘，避免文字被暗背景吞掉。
  ctx.save();
  ctx.filter = 'blur(1.2px)';
  ctx.globalAlpha = 0.26;
  ctx.lineWidth = Math.max(3.2, fontSize * 0.030);
  ctx.strokeStyle = 'rgba(255,255,255,1)';
  strokeLines(0, 0);
  ctx.restore();

  // 转为纹理供可读性 mesh 使用。
  var tex = new THREE.CanvasTexture(canvas);
  tex.minFilter = THREE.LinearFilter;
  tex.magFilter = THREE.LinearFilter;
  tex.generateMipmaps = false;
  tex.anisotropy = Math.min(8, renderer.capabilities.getMaxAnisotropy ? renderer.capabilities.getMaxAnisotropy() : 1);
  return tex;
}

// 为歌词生成扩散辉光贴图。
function makeLyricGlowTexture(text, fontSize, textWidth, lines, lineHeight, fitScaleX) {
  // 清理文本并决定实际绘制行。
  text = String(text || '').replace(/\s+/g, ' ').trim();
  var drawLines = Array.isArray(lines) && lines.length ? lines : [text];
  // 辉光 canvas 会按文字实际尺寸动态创建。
  var canvas = document.createElement('canvas');
  // 单独测量 canvas 用于计算辉光贴图尺寸。
  var measureCanvas = document.createElement('canvas');
  var measureCtx = measureCanvas.getContext('2d');
  measureCtx.font = lyricFontCss(fontSize);
  fitScaleX = fitScaleX || 1;
  // 计算所有行中实际最宽的文本宽度。
  var measuredWidth = Math.max(1, textWidth || lyricMeasureText(measureCtx, text, fontSize) * fitScaleX);
  for (var li = 0; li < drawLines.length; li++) measuredWidth = Math.max(measuredWidth, lyricMeasureText(measureCtx, drawLines[li], fontSize) * fitScaleX);
  // 辉光贴图需要额外边距容纳模糊半径。
  var padX = Math.max(160, fontSize * 1.45);
  var padY = Math.max(86, fontSize * 0.78);
  // 行高和文本块高度。
  var lh = lineHeight || fontSize * 1.04;
  var blockH = fontSize + (drawLines.length - 1) * lh;
  // 最终辉光贴图尺寸。
  var W = Math.ceil(measuredWidth + padX * 2);
  var H = Math.ceil(blockH + padY * 2);
  canvas.width = W; canvas.height = H;
  // 绘制上下文。
  var ctx = canvas.getContext('2d');
  ctx.clearRect(0, 0, W, H);
  ctx.textAlign = 'center';
  ctx.textBaseline = 'alphabetic';
  ctx.font = lyricFontCss(fontSize);
  // 第一行基线。
  var y0 = H / 2 - blockH / 2 + fontSize * 0.82;
  // 按偏移绘制所有辉光文字。
  function drawGlowText(dx, dy) {
    for (var i = 0; i < drawLines.length; i++) {
      var y = y0 + i * lh + (dy || 0);
      if (fitScaleX < 1) {
        // 与遮罩一致，超宽歌词使用水平缩放。
        ctx.save();
        ctx.translate(W / 2 + (dx || 0), 0);
        ctx.scale(fitScaleX, 1);
        if (ctx.lineWidth > 0) lyricStrokeText(ctx, drawLines[i], 0, y, fontSize);
        lyricFillText(ctx, drawLines[i], 0, y, fontSize);
        ctx.restore();
      } else {
        if (ctx.lineWidth > 0) lyricStrokeText(ctx, drawLines[i], W / 2 + (dx || 0), y, fontSize);
        lyricFillText(ctx, drawLines[i], W / 2 + (dx || 0), y, fontSize);
      }
    }
  }
  // 小半径强辉光。
  ctx.save();
  ctx.filter = 'blur(14px)';
  ctx.globalAlpha = 0.46;
  ctx.fillStyle = '#fff';
  ctx.lineWidth = Math.max(10, fontSize * 0.10);
  ctx.strokeStyle = '#fff';
  drawGlowText(0, 0);
  ctx.restore();
  // 中半径辉光。
  ctx.save();
  ctx.filter = 'blur(34px)';
  ctx.globalAlpha = 0.34;
  ctx.fillStyle = '#fff';
  ctx.lineWidth = Math.max(18, fontSize * 0.18);
  ctx.strokeStyle = '#fff';
  drawGlowText(0, 0);
  ctx.restore();
  // 大半径环境辉光。
  ctx.save();
  ctx.filter = 'blur(78px)';
  ctx.globalAlpha = 0.22;
  ctx.fillStyle = '#fff';
  ctx.lineWidth = Math.max(28, fontSize * 0.26);
  ctx.strokeStyle = '#fff';
  drawGlowText(0, 0);
  ctx.restore();
  // 极大范围弱辉光，形成舞台光晕。
  ctx.save();
  ctx.filter = 'blur(116px)';
  ctx.globalAlpha = 0.13;
  ctx.fillStyle = '#fff';
  ctx.lineWidth = Math.max(42, fontSize * 0.40);
  ctx.strokeStyle = '#fff';
  drawGlowText(0, 0);
  ctx.restore();
  // 周向轻微重复绘制，让辉光边缘更饱满。
  ctx.save();
  ctx.globalCompositeOperation = 'lighter';
  ctx.filter = 'blur(8px)';
  ctx.globalAlpha = 0.26;
  ctx.fillStyle = '#fff';
  for (var ri = 0; ri < 8; ri++) {
    // 围绕文字周边偏移采样。
    var ang = ri / 8 * Math.PI * 2;
    drawGlowText(Math.cos(ang) * 7, Math.sin(ang) * 4);
  }
  ctx.restore();
  // 用水平和垂直渐变遮罩裁掉贴图边缘。
  ctx.save();
  ctx.globalCompositeOperation = 'destination-in';
  // 水平淡出遮罩。
  var xMask = ctx.createLinearGradient(0, 0, W, 0);
  xMask.addColorStop(0.00, 'rgba(255,255,255,0)');
  xMask.addColorStop(0.10, 'rgba(255,255,255,1)');
  xMask.addColorStop(0.90, 'rgba(255,255,255,1)');
  xMask.addColorStop(1.00, 'rgba(255,255,255,0)');
  ctx.fillStyle = xMask;
  ctx.fillRect(0, 0, W, H);
  // 垂直淡出遮罩。
  var yMask = ctx.createLinearGradient(0, 0, 0, H);
  yMask.addColorStop(0.00, 'rgba(255,255,255,0)');
  yMask.addColorStop(0.16, 'rgba(255,255,255,1)');
  yMask.addColorStop(0.84, 'rgba(255,255,255,1)');
  yMask.addColorStop(1.00, 'rgba(255,255,255,0)');
  ctx.fillStyle = yMask;
  ctx.fillRect(0, 0, W, H);
  ctx.restore();
  // 转为 Three.js 纹理，并把尺寸元数据写入 userData。
  var tex = new THREE.CanvasTexture(canvas);
  tex.minFilter = THREE.LinearFilter;
  tex.magFilter = THREE.LinearFilter;
  tex.generateMipmaps = false;
  tex.userData = { width:W, height:H, textWidth:measuredWidth };
  return tex;
}

// 歌词太阳辉光纹理缓存。
var lyricSunBloomTexture = null;
// 获取或生成歌词后方的椭圆太阳辉光纹理。
function getLyricSunBloomTexture() {
  // 已生成时直接复用。
  if (lyricSunBloomTexture) return lyricSunBloomTexture;
  // 大尺寸 canvas 用于承载横向椭圆辉光。
  var canvas = document.createElement('canvas');
  canvas.width = 1024; canvas.height = 512;
  // 绘制上下文。
  var ctx = canvas.getContext('2d');
  ctx.clearRect(0, 0, canvas.width, canvas.height);
  // 中心点。
  var cx = canvas.width * 0.50, cy = canvas.height * 0.50;
  // 主径向辉光先通过横向缩放变成椭圆。
  ctx.save();
  ctx.translate(cx, cy);
  ctx.scale(2.05, 1);
  var radial = ctx.createRadialGradient(0, 0, 0, 0, 0, canvas.height * 0.43);
  radial.addColorStop(0.00, 'rgba(255,246,186,0.92)');
  radial.addColorStop(0.18, 'rgba(255,219,126,0.44)');
  radial.addColorStop(0.46, 'rgba(255,186,82,0.15)');
  radial.addColorStop(1.00, 'rgba(255,186,82,0)');
  ctx.fillStyle = radial;
  ctx.fillRect(-canvas.width, -canvas.height, canvas.width * 2, canvas.height * 2);
  ctx.restore();
  // 叠加多层更柔和的暖色椭圆辉光。
  ctx.save();
  ctx.globalCompositeOperation = 'lighter';
  ctx.filter = 'blur(34px)';
  ctx.fillStyle = 'rgba(255,235,168,0.18)';
  ctx.beginPath();
  ctx.ellipse(cx, cy, canvas.width * 0.33, canvas.height * 0.14, -0.06, 0, Math.PI * 2);
  ctx.fill();
  ctx.filter = 'blur(58px)';
  ctx.fillStyle = 'rgba(255,214,122,0.11)';
  ctx.beginPath();
  ctx.ellipse(cx, cy, canvas.width * 0.45, canvas.height * 0.19, -0.05, 0, Math.PI * 2);
  ctx.fill();
  ctx.filter = 'blur(18px)';
  var core = ctx.createRadialGradient(cx, cy, 0, cx, cy, canvas.width * 0.16);
  core.addColorStop(0.00, 'rgba(255,252,220,0.38)');
  core.addColorStop(0.34, 'rgba(255,230,158,0.20)');
  core.addColorStop(1.00, 'rgba(255,210,116,0)');
  ctx.fillStyle = core;
  ctx.fillRect(0, 0, canvas.width, canvas.height);
  ctx.restore();
  // 边缘淡出遮罩，避免平面边界可见。
  ctx.save();
  ctx.globalCompositeOperation = 'destination-in';
  // 水平淡出。
  var xMask = ctx.createLinearGradient(0, 0, canvas.width, 0);
  xMask.addColorStop(0.00, 'rgba(255,255,255,0)');
  xMask.addColorStop(0.11, 'rgba(255,255,255,1)');
  xMask.addColorStop(0.89, 'rgba(255,255,255,1)');
  xMask.addColorStop(1.00, 'rgba(255,255,255,0)');
  ctx.fillStyle = xMask;
  ctx.fillRect(0, 0, canvas.width, canvas.height);
  // 垂直淡出。
  var yMask = ctx.createLinearGradient(0, 0, 0, canvas.height);
  yMask.addColorStop(0.00, 'rgba(255,255,255,0)');
  yMask.addColorStop(0.18, 'rgba(255,255,255,1)');
  yMask.addColorStop(0.82, 'rgba(255,255,255,1)');
  yMask.addColorStop(1.00, 'rgba(255,255,255,0)');
  ctx.fillStyle = yMask;
  ctx.fillRect(0, 0, canvas.width, canvas.height);
  ctx.restore();
  // 转为纹理并缓存。
  lyricSunBloomTexture = new THREE.CanvasTexture(canvas);
  lyricSunBloomTexture.minFilter = THREE.LinearFilter;
  lyricSunBloomTexture.magFilter = THREE.LinearFilter;
  lyricSunBloomTexture.generateMipmaps = false;
  return lyricSunBloomTexture;
}

// 创建歌词文字本体使用的 shader 材质。
function makeLyricShaderMaterial(mask, pal) {
  return new THREE.ShaderMaterial({
    uniforms: {
      // 文字 alpha 遮罩。
      uMap: { value: mask.texture },
      // 卡拉 OK 进度，控制高亮区域。
      uProgress: { value: 0 },
      // 文字实际横向范围，用于把进度映射到文本宽度。
      uTextMin: { value: mask.textMin },
      uTextMax: { value: mask.textMax },
      // 整体透明度。
      uOpacity: { value: 0 },
      // 基础文字颜色。
      uBaseColor: { value: lyricThreeColor(pal.primary, '#d6f8ff', 0.38) },
      // 已唱进度高亮颜色。
      uHiColor: { value: lyricThreeColor(pal.highlight || pal.primary, '#fff0b8', 0.48) },
      // 进度边缘辉光颜色。
      uGlowColor: { value: lyricThreeColor(pal.glowColor || pal.secondary, '#9cffdf', 0.36) },
      // 太阳暖光颜色。
      uSolarColor: { value: lyricThreeColor(pal.highlight || pal.secondary || pal.primary, '#fff0b8', 0.50) },
      // 原生逐字歌词使用更窄羽化，没有逐字时更柔和。
      uFeather: { value: lyricsHasNativeKaraoke ? 0.100 : 0.220 },
      // 太阳暖光混合强度。
      uSolar: { value: 0 },
    },
    vertexShader: 'varying vec2 vUv; void main(){ vUv=uv; gl_Position=projectionMatrix*modelViewMatrix*vec4(position,1.0); }',
    fragmentShader: [
      'precision highp float;',
      'uniform sampler2D uMap;',
      'uniform float uProgress,uTextMin,uTextMax,uOpacity,uFeather,uSolar;',
      'uniform vec3 uBaseColor,uHiColor,uGlowColor,uSolarColor;',
      'varying vec2 vUv;',
      'void main(){',
      '  vec2 uv = gl_FrontFacing ? vUv : vec2(1.0 - vUv.x, vUv.y);',
      '  float mask = texture2D(uMap, uv).a;',
      '  if(mask < 0.01) discard;',
      '  float denom = max(0.001, uTextMax - uTextMin);',
      '  float p = clamp((uv.x - uTextMin) / denom, 0.0, 1.0);',
      '  float filled = 1.0 - smoothstep(uProgress, uProgress + uFeather, p);',
      '  float edge = 1.0 - smoothstep(0.0, uFeather * 2.8, abs(p - uProgress));',
      '  vec3 color = mix(uBaseColor, uHiColor, filled * 0.88);',
      '  color += uGlowColor * edge * 0.14;',
      '  vec3 solar = uSolarColor;',
      '  color = mix(color, color + solar * 0.34, uSolar * (0.25 + filled * 0.45));',
      '  color += solar * edge * uSolar * 0.22;',
      '  float lum = dot(color, vec3(0.299, 0.587, 0.114));',
      '  color += vec3(max(0.0, 0.30 - lum));',
      '  gl_FragColor = vec4(color, mask * uOpacity);',
      '}',
    ].join('\n'),
    transparent:true, depthWrite:false, depthTest:false, side:THREE.DoubleSide,
  });
}

// 根据文本构建完整舞台歌词 mesh 组。
function buildLyricMesh(text) {
  // 归一化文本空白。
  text = String(text || '').replace(/\s+/g, ' ').trim();
  // 先生成文字遮罩。
  var mask = makeLyricMask(text);
  // 使用当前舞台歌词色板。
  var pal = stageLyrics.palette;
  // 歌词平面基础世界宽度。
  var worldW = 6.10;
  // 根据遮罩纵横比计算世界高度。
  var worldH = worldW * (mask.height / mask.width);
  // 文字平面几何。
  var geo = new THREE.PlaneGeometry(worldW, worldH, 1, 1);
  // 文字实际内容在世界空间中的宽高。
  var textWorldW = worldW * (mask.textWidth / mask.width);
  var textWorldH = worldH * ((mask.textHeight || mask.fontSize) / mask.height);
  // 完整歌词组，包含太阳、辉光、可读性层、文字和火花。
  var group = new THREE.Group();
  group.renderOrder = 42;
  group.position.set((Math.random() - 0.5) * 0.08, 0.20, 1.46);
  group.scale.setScalar(0.96);
  group.userData.age = 0;
  group.userData.state = 'in';
  group.userData.lastLyricProgress = -1;
  group.userData.floatSeed = Math.random() * 100;

  // 太阳辉光材质，位于歌词后方。
  var sunMat = new THREE.MeshBasicMaterial({
    map:getLyricSunBloomTexture(), transparent:true, opacity:0,
    depthWrite:false, depthTest:false, side:THREE.DoubleSide,
    blending:THREE.AdditiveBlending, color:lyricThreeColor(pal.highlight || pal.secondary || pal.primary, '#ffe7a6', 0.50)
  });
  // 根据文字实际宽高计算太阳辉光平面尺寸。
  var sunWorldW = Math.max(textWorldW + worldH * 1.10, textWorldW * 1.18);
  sunWorldW = Math.min(worldW * 1.16, Math.max(worldH * 1.35, sunWorldW));
  var sunWorldH = Math.max(worldH * 1.02, Math.min(worldH * 1.54, worldH + textWorldW * 0.070));
  // 太阳辉光 mesh。
  var sun = new THREE.Mesh(new THREE.PlaneGeometry(sunWorldW, sunWorldH, 1, 1), sunMat);
  sun.renderOrder = 40;
  sun.position.set(0, 0.02, -0.030);
  sun.scale.set(0.78, 0.58, 1);
  group.add(sun);

  // 文字辉光贴图和材质。
  var glowTex = makeLyricGlowTexture(text, mask.fontSize, mask.textWidth, mask.lines, mask.lineHeight, mask.fitScaleX);
  var glowMat = new THREE.MeshBasicMaterial({
    map: glowTex, transparent:true, opacity:0, depthWrite:false, depthTest:false,
    side:THREE.DoubleSide, blending:THREE.AdditiveBlending, color:lyricThreeColor(pal.secondary, '#9cffdf', 0.36)
  });
  // 读取辉光贴图元数据用于换算世界尺寸。
  var glowMeta = glowTex.userData || {};
  // 辉光平面宽度按贴图实际宽度映射。
  var glowWorldW = textWorldW * ((glowMeta.width || mask.width) / Math.max(1, glowMeta.textWidth || mask.textWidth));
  glowWorldW = Math.min(worldW * 1.10, Math.max(textWorldW + worldH * 0.38, glowWorldW));
  var glowWorldH = worldH * ((glowMeta.height || mask.height) / mask.height);
  glowWorldH = Math.min(worldH * 1.42, Math.max(worldH * 0.92, glowWorldH));
  // 辉光 mesh 位于文字后方。
  var glow = new THREE.Mesh(new THREE.PlaneGeometry(glowWorldW, glowWorldH, 1, 1), glowMat);
  glow.renderOrder = 41;
  glow.scale.set(1.0, 1.06, 1);
  group.add(glow);

  // 可读性层贴图和材质。
  var readabilityTex = makeLyricReadabilityTexture(mask);
  var readabilityMat = new THREE.MeshBasicMaterial({
    map: readabilityTex, transparent:true, opacity:0, depthWrite:false, depthTest:false,
    side:THREE.DoubleSide
  });
  // 可读性层和文字平面同尺寸，只在文字描边区域有 alpha。
  var readability = new THREE.Mesh(new THREE.PlaneGeometry(worldW, worldH, 1, 1), readabilityMat);
  readability.renderOrder = 42;
  readability.position.set(0, 0, -0.012);
  group.add(readability);

  // 文字本体 shader 和 mesh。
  var textMat = makeLyricShaderMaterial(mask, pal);
  var textMesh = new THREE.Mesh(geo, textMat);
  textMesh.renderOrder = 43;
  group.add(textMesh);

  // 歌词周围火花粒子数量。
  var sparkCount = 132;
  // 火花粒子几何。
  var pgeo = new THREE.BufferGeometry();
  // 火花粒子位置数组。
  var ppos = new Float32Array(sparkCount * 3);
  // 火花粒子随机种子。
  var pseed = new Float32Array(sparkCount);
  for (var i = 0; i < sparkCount; i++) {
    // 用椭圆环分布在文字周围。
    var angle = Math.random() * Math.PI * 2;
    var ring = 0.78 + Math.pow(Math.random(), 1.45) * 0.58;
    var rx = textWorldW * (0.50 + Math.random() * 0.22) + 0.10;
    var ry = worldH * (0.42 + Math.random() * 0.22) + 0.08;
    ppos[i*3] = Math.cos(angle) * rx * ring + (Math.random() - 0.5) * textWorldW * 0.12;
    ppos[i*3+1] = Math.sin(angle) * ry * ring + (Math.random() - 0.5) * worldH * 0.14;
    ppos[i*3+2] = (Math.random() - 0.5) * 0.24;
    pseed[i] = Math.random() * 1000;
  }
  pgeo.setAttribute('position', new THREE.BufferAttribute(ppos, 3));
  pgeo.setAttribute('seed', new THREE.BufferAttribute(pseed, 1));
  // 火花粒子材质，shader 中按 seed 控制大小和闪烁。
  var pmat = new THREE.ShaderMaterial({
    uniforms: {
      uMap: { value: dotTexture },
      uSize: { value: 0.052 },
      uOpacity: { value: 0 },
      uColor: { value: lyricThreeColor(pal.highlight || pal.secondary || pal.primary, '#fff7d2', 0.30) },
      uPixel: uniforms.uPixel
    },
    vertexShader: [
      'attribute float seed;',
      'uniform float uSize;',
      'uniform float uPixel;',
      'varying float vSeed;',
      'void main(){',
      '  vSeed = seed;',
      '  vec4 mv = modelViewMatrix * vec4(position, 1.0);',
      '  float jitter = 0.58 + fract(sin(seed * 19.17) * 43758.5453) * 1.18;',
      '  float depth = clamp(2.2 / max(0.35, -mv.z), 0.54, 1.55);',
      '  gl_PointSize = uSize * jitter * depth * uPixel * 120.0;',
      '  gl_Position = projectionMatrix * mv;',
      '}'
    ].join('\n'),
    fragmentShader: [
      'precision highp float;',
      'uniform sampler2D uMap;',
      'uniform vec3 uColor;',
      'uniform float uOpacity;',
      'varying float vSeed;',
      'void main(){',
      '  vec4 tex = texture2D(uMap, gl_PointCoord);',
      '  float twinkle = 0.72 + fract(sin(vSeed * 7.31) * 91.7) * 0.28;',
      '  gl_FragColor = vec4(uColor * twinkle, tex.a * uOpacity);',
      '}'
    ].join('\n'),
    transparent:true, depthWrite:false, depthTest:false, blending:THREE.AdditiveBlending
  });
  // 火花粒子对象。
  var sparks = new THREE.Points(pgeo, pmat);
  sparks.renderOrder = 44;
  sparks.visible = !!fx.lyricGlowParticles;
  group.add(sparks);

  // 把后续更新所需的材质、尺寸和基础粒子位置都挂到 userData。
  group.userData.lyric = {
    mask:mask, textMesh:textMesh, readability:readability, glow:glow, sparks:sparks, sun:sun,
    textMat:textMat, readabilityMat:readabilityMat, glowMat:glowMat, sparkMat:pmat, sunMat:sunMat,
    basePositions:ppos.slice ? ppos.slice(0) : new Float32Array(ppos),
    textWorldW:textWorldW, textWorldH:textWorldH, worldW:worldW, worldH:worldH
  };
  // 初始没有歌词进度时写入默认进度状态。
  updateLyricMeshProgress(group, null);
  return group;
}

// 更新单个歌词 mesh 的卡拉 OK 进度。
function updateLyricMeshProgress(mesh, progress) {
  // 没有歌词数据时跳过。
  if (!mesh || !mesh.userData || !mesh.userData.lyric) return;
  // progress 为 null 表示没有有效逐字进度。
  var hasProgress = progress != null && isFinite(progress);
  // 有效进度裁剪到 0..1，无效进度写 -1 让 shader 不显示已唱高亮。
  progress = hasProgress ? Math.max(0, Math.min(1, progress || 0)) : -1;
  // 读取歌词数据并写入 shader uniform。
  var d = mesh.userData.lyric;
  d.textMat.uniforms.uProgress.value = progress;
  // 保存上一帧进度，用于样式重绘后恢复。
  mesh.userData.lastLyricProgress = hasProgress ? progress : 0;
  mesh.userData.hasLyricProgress = hasProgress;
}

// 显示一行舞台歌词。
function showStageLine(text, redrawOnly) {
  // 确保歌词分组已经创建。
  createLyricsParticles();
  if (!stageLyrics.group) return;
  // 空文本表示清空歌词。
  if (!text) { clearStageLyrics(); return; }
  if (redrawOnly && stageLyrics.current) {
    // 样式刷新时直接销毁当前 mesh，避免把旧样式放入淡出队列。
    disposeLyricMesh(stageLyrics.current);
    stageLyrics.current = null;
  } else if (stageLyrics.current) {
    // 正常切句时把当前歌词转入淡出队列。
    stageLyrics.current.userData.state = 'out';
    stageLyrics.current.userData.age = 0;
    stageLyrics.outgoing.push(stageLyrics.current);
  }
  // 保存当前文本，后续刷新样式时复用。
  stageLyrics.currentText = text;
  // 构建新歌词 mesh 并挂到舞台歌词分组。
  var mesh = buildLyricMesh(text);
  stageLyrics.group.add(mesh);
  stageLyrics.current = mesh;
}

// 当前歌词样式变更后重建 mesh，并尽量保留原进度。
function refreshCurrentLyricStyle() {
  // 没有当前歌词时无需刷新。
  if (!stageLyrics || !stageLyrics.currentText || !stageLyrics.current) return;
  // 读取旧 mesh 中保存的歌词进度。
  var userData = stageLyrics.current.userData || {};
  var progress = userData.hasLyricProgress ? (userData.lastLyricProgress || 0) : null;
  // redrawOnly=true 表示只重绘当前样式。
  showStageLine(stageLyrics.currentText, true);
  // 恢复重建前的进度。
  updateLyricMeshProgress(stageLyrics.current, progress);
  // 给新 mesh 一个接近已入场状态的 age，避免样式切换时重新大幅淡入。
  if (stageLyrics.current && stageLyrics.current.userData) stageLyrics.current.userData.age = 0.48;
}

// 清空当前舞台歌词和所有淡出歌词。
function clearStageLyrics() {
  // 释放当前歌词 mesh。
  disposeLyricMesh(stageLyrics.current);
  stageLyrics.current = null;
  // 重置歌词索引和文本缓存。
  stageLyrics.currentIdx = -1;
  stageLyrics.currentText = '';
  // 释放淡出队列中的历史歌词。
  while (stageLyrics.outgoing.length) disposeLyricMesh(stageLyrics.outgoing.pop());
}

// 每帧更新舞台歌词的位置、朝向、透明度、辉光和粒子。
function updateStageLyrics3D(dt) {
  // 分组未创建时无需更新。
  if (!stageLyrics.group) return;
  // 未启用粒子歌词且没有可见歌词时跳过。
  if (!fx.particleLyrics && !stageLyrics.current && (!stageLyrics.outgoing || !stageLyrics.outgoing.length)) return;
  // 防止外部异常把缓存数值污染成 NaN。
  if (!isFinite(stageLyrics.highBloom)) stageLyrics.highBloom = 0;
  if (!isFinite(stageLyrics.beatGlow)) stageLyrics.beatGlow = 0;
  if (!isFinite(stageLyrics.glowFollowX)) stageLyrics.glowFollowX = 0;
  if (!isFinite(stageLyrics.glowFollowY)) stageLyrics.glowFollowY = 0;
  if (!isFinite(stageLyrics.glowFollowRoll)) stageLyrics.glowFollowRoll = 0;
  // 当前全局时间。
  var t = uniforms.uTime.value;
  // 歌词辉光强度，关闭时为 0。
  var lyricGlowStrength = fx.lyricGlow ? Math.min(0.85, Math.max(0, fx.lyricGlowStrength)) : 0;
  // 将用户辉光强度换算成内部驱动倍率。
  var glowDrive = Math.min(1.7, Math.max(0, lyricGlowStrength / 0.50));
  // 慢速呼吸项让辉光不完全静止。
  var glowBreath = lyricGlowStrength > 0 ? (0.5 + 0.5 * Math.sin(t * 1.05)) : 0;
  // 音乐能量和节拍共同驱动太阳辉光。
  var musicBloom = Math.max(lyricSunEnergy, beatPulse * 0.10);
  // 节拍跟随辉光只在对应开关开启时生效。
  var beatGlowRaw = fx.lyricGlowBeat && lyricGlowStrength > 0
    ? Math.max(beatPulse * 1.22, beatCam.punch * 0.86 + beatCam.radiusKick * 1.85)
    : 0;
  // 节拍辉光快速上升、慢速下降。
  stageLyrics.beatGlow += (beatGlowRaw - stageLyrics.beatGlow) * (beatGlowRaw > stageLyrics.beatGlow ? 0.32 : 0.10);
  if (!isFinite(stageLyrics.beatGlow)) stageLyrics.beatGlow = 0;
  // 骷髅预设下歌词辉光需要单独降低底噪并加强瞬态。
  var skullLyricPreset = !!(fx && fx.preset === SKULL_PRESET_INDEX);
  // 普通舞台太阳辉光目标。
  var solarBloom = lyricGlowStrength > 0 ? (0.18 + glowBreath * 0.16 + musicBloom * 0.90 + stageLyrics.beatGlow * 1.18 + Math.sin(t * 0.37 + 1.2) * 0.035) * glowDrive : 0;
  if (skullLyricPreset && lyricGlowStrength > 0) {
    // 骷髅预设使用更低常亮和更强的节拍/闪光响应。
    solarBloom = (0.035 + glowBreath * 0.030 + musicBloom * 0.11 + Math.pow(Math.max(0, stageLyrics.beatGlow), 1.26) * 1.45 + Math.pow(Math.max(0, skullBeatFlash || 0), 1.08) * 1.18) * glowDrive;
  }
  // 限制太阳辉光上限。
  solarBloom = Math.max(0, Math.min(1.45, solarBloom));
  // 高亮辉光按目标缓动。
  stageLyrics.highBloom += (solarBloom - stageLyrics.highBloom) * (solarBloom > stageLyrics.highBloom ? (skullLyricPreset ? 0.22 : 0.075) : (skullLyricPreset ? 0.070 : 0.050));
  if (!isFinite(stageLyrics.highBloom)) stageLyrics.highBloom = 0;
  // 更新歌词后方星河。
  updateLyricStarRiver(dt);
  // 计算辉光跟随相机节拍运动的驱动强度。
  var followDrive = fx.lyricGlowBeat && lyricGlowStrength > 0 ? Math.min(1.35, stageLyrics.beatGlow) : 0;
  var followXTarget = followDrive * (beatCam.thetaKick * 34 + beatCam.rollKick * 8);
  var followYTarget = followDrive * (beatCam.phiKick * 42 - beatCam.radiusKick * 0.48);
  var followRollTarget = followDrive * (beatCam.rollKick * 22 + beatCam.thetaKick * 10);
  stageLyrics.glowFollowX += (followXTarget - stageLyrics.glowFollowX) * 0.26;
  stageLyrics.glowFollowY += (followYTarget - stageLyrics.glowFollowY) * 0.24;
  stageLyrics.glowFollowRoll += (followRollTarget - stageLyrics.glowFollowRoll) * 0.22;
  stageLyrics.glowFollowX *= 0.92;
  stageLyrics.glowFollowY *= 0.92;
  stageLyrics.glowFollowRoll *= 0.90;
  // 读取用户歌词布局配置。
  var layoutScale = clampRange(Number(fx.lyricScale) || 1, 0.35, 1.65);
  var layoutX = clampRange(Number(fx.lyricOffsetX) || 0, -2.0, 2.0);
  var layoutY = clampRange(Number(fx.lyricOffsetY) || 0, -1.2, 1.35);
  var layoutZ = clampRange(Number(fx.lyricOffsetZ) || 0, -1.6, 1.6);
  var layoutTiltX = clampRange(Number(fx.lyricTiltX) || 0, -42, 42);
  var layoutTiltY = clampRange(Number(fx.lyricTiltY) || 0, -42, 42);
  // 骷髅预设下歌词可以贴近嘴部。
  var skullMouthLyrics = !!(camera && fx && fx.preset === SKULL_PRESET_INDEX && skullParticleGroup && skullParticleGroup.visible);
  // 歌单架二级详情是否打开。
  var shelfDetailOpen = !!(shelfManager && shelfManager.hasOpenContent && shelfManager.hasOpenContent());
  // 骷髅与普通预设下的歌单架详情分别处理。
  var skullShelfDetailOpen = !!(fx && fx.preset === SKULL_PRESET_INDEX && shelfDetailOpen);
  var normalShelfDetailOpen = !!(shelfDetailOpen && !skullShelfDetailOpen);
  // 歌单架详情打开时降低歌词渲染顺序，避免遮住内容。
  stageLyrics.group.renderOrder = shelfDetailOpen ? 24 : 38;
  // 歌单架详情打开时整体压低歌词亮度和辉光。
  var shelfDetailLyricProfile = shelfDetailOpen ? {
    opacity: skullShelfDetailOpen ? 0.30 : 0.38,
    readability: skullShelfDetailOpen ? 0.20 : 0.26,
    bloom: skullShelfDetailOpen ? 0.20 : 0.24,
    glowCap: skullShelfDetailOpen ? 0.050 : 0.070,
    outgoing: skullShelfDetailOpen ? 0.34 : 0.42,
    easeDown: 0.34
  } : {
    opacity: 0.96,
    readability: 0.86,
    bloom: 1,
    glowCap: 1.0,
    outgoing: 1,
    easeDown: 0.16
  };
  // 是否需要为歌单架避让舞台歌词。
  var shelfLyricAvoid = shouldAvoidStageLyricsForShelf();
  // 壁纸模式下是否使用相机锁定歌词。
  var wallpaperLyricLock = shouldUseWallpaperLyricCameraLock();
  // 壁纸和歌单架组合时需要进一步压暗并偏移歌词。
  var wallpaperShelfLyrics = wallpaperLyricLock && shouldDimWallpaperForShelf();
  if (wallpaperLyricLock) {
    // 壁纸锁定模式下歌词更靠近相机，同时给歌单架留出空间。
    layoutScale *= wallpaperShelfLyrics ? 0.60 : 0.84;
    layoutX = clampRange(layoutX + (wallpaperShelfLyrics ? -1.34 : 0), -2.0, 2.0);
    layoutY = clampRange(layoutY + (wallpaperShelfLyrics ? -0.04 : 0.08), -1.2, 1.35);
    layoutZ = clampRange(layoutZ + (wallpaperShelfLyrics ? 1.02 : 1.15), -1.6, 1.6);
  } else if (!skullMouthLyrics && shelfLyricAvoid && fx.lyricCameraLock) {
    // 普通相机锁定歌词遇到歌单架时向左缩小避让。
    layoutScale *= 0.72;
    layoutX = clampRange(layoutX - 1.36, -2.0, 2.0);
    layoutY = clampRange(layoutY + 0.06, -1.2, 1.35);
    layoutZ = clampRange(layoutZ + 0.72, -1.6, 1.6);
  } else if (!skullMouthLyrics && shouldOffsetLyricsForShelfDetail()) {
    // 歌单架详情打开时，非锁定歌词也需要偏移。
    layoutScale *= normalShelfDetailOpen ? 0.56 : 0.70;
    layoutX = clampRange(layoutX - (normalShelfDetailOpen ? 1.78 : 1.58), -2.0, 2.0);
    layoutY = clampRange(layoutY + (normalShelfDetailOpen ? 0.18 : 0.08), -1.2, 1.35);
    layoutZ = clampRange(layoutZ + 0.84, -1.6, 1.6);
  }
  if (skullMouthLyrics) {
    // 嘴部歌词更小，防止覆盖骷髅面部。
    layoutScale *= skullShelfDetailOpen ? 0.52 : (shelfLyricAvoid ? 0.58 : 0.66);
    if (shelfLyricAvoid && !skullShelfDetailOpen) {
      layoutX = clampRange(layoutX - 0.36, -2.0, 2.0);
      layoutY = clampRange(layoutY + 0.02, -1.2, 1.35);
      layoutZ = clampRange(layoutZ + 0.18, -1.6, 1.6);
    }
  }
  // 相机锁定模式下的基准距离。
  var lockBaseDistance = wallpaperShelfLyrics ? 5.58 : 4.85;
  // 用户 Z 偏移叠加到锁定距离。
  var lockDistance = lockBaseDistance + layoutZ;
  // 是否采用相机锁定歌词。
  var cameraLockedLyrics = (fx.lyricCameraLock || wallpaperLyricLock) && camera;
  // 骷髅回正过程中也需要边缘保护缩放。
  var skullLyricEdgeGuard = !!(fx && fx.preset === SKULL_PRESET_INDEX && (orbit.centerLocked || orbit.recentering));
  // 计算当前构图下的安全缩放。
  var lockFit = (cameraLockedLyrics || skullLyricEdgeGuard || skullMouthLyrics) ? lyricCameraLockFit(layoutScale, layoutX, layoutY, skullMouthLyrics ? Math.max(2.2, 4.4 + layoutZ) : lockDistance) : 1;
  if (skullMouthLyrics) lockFit = Math.min(lockFit, 1.12);
  if (!isFinite(stageLyrics.lockFitScale)) stageLyrics.lockFitScale = 1;
  // 安全缩放平滑变化，缩小时更快。
  stageLyrics.lockFitScale += (lockFit - stageLyrics.lockFitScale) * (lockFit < stageLyrics.lockFitScale ? 0.18 : 0.10);
  stageLyrics.group.scale.setScalar(layoutScale * stageLyrics.lockFitScale);
  if (skullMouthLyrics) {
    // 嘴部歌词完全跟随骷髅模型，不触发相机锁定 snap。
    stageLyrics.snapCameraLockFrames = 0;
    // 先更新骷髅矩阵，再把嘴部本地坐标转成世界坐标。
    skullParticleGroup.updateMatrixWorld(true);
    skullLyricMouthTarget.copy(skullLyricMouthLocal).applyMatrix4(skullParticleGroup.matrixWorld);
    skullParticleGroup.getWorldQuaternion(skullLyricMouthQuat);
    skullLyricMouthForward.set(0, 0, 1).applyQuaternion(skullLyricMouthQuat);
    skullLyricMouthTarget.addScaledVector(skullLyricMouthForward, 0.020);
    // 使用骷髅嘴部朝向作为歌词朝向基础。
    skullLyricReadableQuat.copy(skullLyricMouthQuat);
    setStageLyricViewBasisFromCameraOrQuaternion(skullLyricMouthQuat);
    lyricLayoutTarget.copy(skullLyricMouthTarget);
    applyStageLyricLayoutOffset(lyricLayoutTarget, layoutX, layoutY, layoutZ);
    stageLyricTargetQuaternion(skullLyricReadableQuat, layoutTiltX, layoutTiltY);
    stageLyrics.group.userData = stageLyrics.group.userData || {};
    if (!stageLyrics.group.userData.skullMouthLocked) {
      // 首次进入嘴部锁定时直接贴合，避免从旧位置飞过去。
      stageLyrics.group.position.copy(lyricLayoutTarget);
      stageLyrics.group.quaternion.copy(lyricTargetQuat);
      stageLyrics.group.userData.skullMouthLocked = true;
    } else {
      // 后续帧平滑跟随嘴部。
      stageLyrics.group.position.lerp(lyricLayoutTarget, 0.26);
      stageLyrics.group.quaternion.slerp(lyricTargetQuat, 0.30);
    }
  } else if (cameraLockedLyrics) {
    // 相机锁定歌词时解除嘴部锁定标记。
    if (stageLyrics.group.userData) stageLyrics.group.userData.skullMouthLocked = false;
    // 使用当前相机作为视图基准。
    setStageLyricViewBasisFromCameraOrQuaternion(null);
    // 基准点位于相机前方固定距离。
    lyricLayoutBase.copy(camera.position).addScaledVector(lyricCameraDir, lockBaseDistance);
    lyricCameraTarget.copy(lyricLayoutBase);
    applyStageLyricLayoutOffset(lyricCameraTarget, layoutX, layoutY, layoutZ);
    stageLyricTargetQuaternion(camera.quaternion, layoutTiltX, layoutTiltY);
    if (stageLyrics.snapCameraLockFrames > 0) {
      // snap 帧内直接贴合，常用于切换后立即稳定歌词位置。
      stageLyrics.group.position.copy(lyricCameraTarget);
      stageLyrics.group.quaternion.copy(lyricTargetQuat);
      stageLyrics.snapCameraLockFrames -= 1;
    } else {
      // 普通锁定使用缓动，壁纸模式稍快。
      var lockPosEase = wallpaperLyricLock ? (wallpaperShelfLyrics ? 0.42 : 0.34) : 0.24;
      var lockQuatEase = wallpaperLyricLock ? (wallpaperShelfLyrics ? 0.44 : 0.36) : 0.22;
      stageLyrics.group.position.lerp(lyricCameraTarget, lockPosEase);
      stageLyrics.group.quaternion.slerp(lyricTargetQuat, lockQuatEase);
    }
  } else {
    // 默认歌词跟随封面粒子平面。
    if (stageLyrics.group.userData) stageLyrics.group.userData.skullMouthLocked = false;
    stageLyrics.snapCameraLockFrames = 0;
    if (particles) {
      // 从主粒子对象读取封面世界位置和朝向。
      particles.updateMatrixWorld(true);
      particles.getWorldPosition(lyricCoverWorldPos);
      particles.getWorldQuaternion(lyricCoverWorldQuat);
    } else {
      // 主粒子不存在时退回世界原点和单位朝向。
      lyricCoverWorldPos.set(0, 0, 0);
      lyricCoverWorldQuat.identity();
    }
    // 使用封面朝向作为歌词视图基准。
    setStageLyricViewBasisFromCameraOrQuaternion(lyricCoverWorldQuat);
    lyricLayoutBase.copy(lyricCoverWorldPos);
    lyricLayoutTarget.copy(lyricLayoutBase);
    applyStageLyricLayoutOffset(lyricLayoutTarget, layoutX, layoutY, layoutZ);
    stageLyrics.group.position.copy(lyricLayoutTarget);
    stageLyricTargetQuaternion(lyricCoverWorldQuat, layoutTiltX, layoutTiltY);
    stageLyrics.group.quaternion.copy(lyricTargetQuat);
  }
  // 更新单个歌词 mesh 的入场/退场、透明度和子层状态。
  function tickMesh(mesh, isCurrent) {
    // 空 mesh 视为已结束。
    if (!mesh) return false;
    // age 驱动入场或退场曲线。
    mesh.userData.age += dt;
    // 当前歌词入场时间略长，淡出歌词退场更快。
    var a = Math.min(1, mesh.userData.age / (isCurrent ? 0.52 : 0.38));
    // smoothstep 曲线。
    a = a * a * (3 - 2 * a);
    // 歌词子层数据。
    var data = mesh.userData.lyric || {};
    // 淡出歌词的辉光跟随幅度降低。
    var followMix = isCurrent ? 1.0 : 0.64;
    var glowX = stageLyrics.glowFollowX * followMix;
    var glowY = stageLyrics.glowFollowY * followMix;
    var glowRoll = stageLyrics.glowFollowRoll * followMix;
    if (data.glow) {
      // 辉光层跟随节拍相机偏移，制造光晕滞后。
      data.glow.position.set(glowX * 0.14, glowY * 0.12, -0.006);
      data.glow.rotation.z = glowRoll * 0.30;
    }
    if (data.sun) {
      // 太阳辉光的跟随幅度更大，增强音乐冲击感。
      data.sun.position.set(glowX * 0.42, 0.02 + glowY * 0.34, -0.035);
      data.sun.rotation.z = glowRoll * 0.36;
    }
    if (data.sparks) {
      // 火花粒子也跟随辉光偏移。
      data.sparks.position.set(glowX * 0.24, glowY * 0.22, 0.010);
      data.sparks.rotation.z = glowRoll * 0.22;
    }
    // 当前 mesh 的文字透明度。
    var opacity = 0;
    if (isCurrent) {
      // 当前歌词按歌单架详情状态压暗。
      var shelfDetailLyricDim = shelfDetailLyricProfile.bloom;
      // 当前歌词目标透明度。
      var lyricOpacityTarget = shelfDetailLyricProfile.opacity;
      // 当前文字材质透明度。
      var currentOpacity = data.textMat ? data.textMat.uniforms.uOpacity.value : 0;
      // 详情打开且需要降低透明度时使用更快 ease。
      var opacityEase = shelfDetailOpen && currentOpacity > lyricOpacityTarget ? shelfDetailLyricProfile.easeDown : 0.16;
      opacity = clampRange(currentOpacity + (lyricOpacityTarget - currentOpacity) * opacityEase, 0, 1);
      if (data.textMat) data.textMat.uniforms.uOpacity.value = opacity;
      if (data.readabilityMat) {
        // 可读性描边透明度跟随文字透明度。
        var readabilityTarget = opacity * shelfDetailLyricProfile.readability;
        var readabilityEase = shelfDetailOpen && data.readabilityMat.opacity > readabilityTarget ? 0.28 : 0.16;
        data.readabilityMat.opacity += (readabilityTarget - data.readabilityMat.opacity) * readabilityEase;
      }
      if (data.textMat && data.textMat.uniforms.uSolar) {
        // 文字 shader 中的暖光强度。
        var solarTarget = stageLyrics.highBloom * shelfDetailLyricDim;
        var solarEase = shelfDetailOpen && data.textMat.uniforms.uSolar.value > solarTarget ? 0.26 : 0.12;
        data.textMat.uniforms.uSolar.value += (solarTarget - data.textMat.uniforms.uSolar.value) * solarEase;
      }
      // 当前暖光强度。
      var solar = stageLyrics.highBloom * shelfDetailLyricDim;
      // 颜色向暖光偏移的程度。
      var warmth = Math.max(0, Math.min(1, solar * 1.10));
      if (data.glowMat) {
        // 辉光层透明度受用户强度、音乐和详情压暗共同影响。
        var glowTarget = lyricGlowStrength > 0 ? Math.min(shelfDetailLyricProfile.glowCap, (0.075 + solar * 0.34 + stageLyrics.beatGlow * 0.16 * shelfDetailLyricDim) * Math.min(3.0, glowDrive)) : 0;
        data.glowMat.opacity += (glowTarget - data.glowMat.opacity) * (glowTarget > data.glowMat.opacity ? 0.095 : (shelfDetailOpen ? 0.20 : 0.055));
        data.glowMat.color.copy(lyricThreeColor(stageLyrics.palette.glowColor || stageLyrics.palette.secondary, '#9cffdf', 0.36)).lerp(lyricSunHotColor, warmth);
      }
      if (data.sparkMat) {
        // 火花只在开启粒子辉光且无详情遮挡时明显显示。
        var sparkTarget = lyricGlowStrength > 0 && fx.lyricGlowParticles && !shelfDetailOpen ? Math.min(0.42, (0.10 + solar * 0.14 + stageLyrics.beatGlow * 0.10) * Math.min(1.6, glowDrive)) : 0;
        // 平滑更新火花透明度和大小。
        var sparkOpacity = getLyricSparkOpacity(data);
        sparkOpacity += (sparkTarget - sparkOpacity) * (sparkTarget > sparkOpacity ? 0.13 : (shelfDetailOpen ? 0.22 : 0.075));
        setLyricSparkOpacity(data, sparkOpacity);
        var sparkSizeTarget = fx.lyricGlowParticles && !shelfDetailOpen ? (0.050 + solar * 0.016 + stageLyrics.beatGlow * 0.026 + bass * 0.008) : 0.035;
        setLyricSparkSize(data, getLyricSparkSize(data) + (sparkSizeTarget - getLyricSparkSize(data)) * 0.12);
        // 火花颜色在暖光和高亮色之间变化。
        var sparkColor = lyricSunHotColor.clone().lerp(lyricSunColor, 0.22 + solar * 0.18);
        setLyricSparkColor(data, sparkColor);
      }
      // 每句歌词有独立随机种子，控制漂浮节奏。
      var seed = mesh.userData.floatSeed || 0;
      if (data.sunMat) {
        // 太阳辉光透明度受音乐暖光驱动。
        var sunTarget = lyricGlowStrength > 0 && !shelfDetailOpen ? Math.min(0.88, (Math.pow(Math.min(1.35, solar), 1.08) * 0.28 + stageLyrics.beatGlow * 0.20) * Math.min(2.4, glowDrive)) : 0;
        data.sunMat.opacity += (sunTarget - data.sunMat.opacity) * (shelfDetailOpen ? 0.18 : 0.055);
        data.sunMat.color.copy(lyricSunColor).lerp(lyricSunHotColor, solar * 0.55);
      }
      if (data.sun) {
        // 太阳辉光大小随音乐呼吸。
        var sunPulse = solar;
        var beatScale = fx.lyricGlowBeat ? stageLyrics.beatGlow * 0.24 : 0;
        data.sun.scale.set(0.82 + sunPulse * 0.36 + beatScale + Math.sin(t * 1.6) * sunPulse * 0.018, 0.60 + sunPulse * 0.34 + beatScale * 0.72 + Math.cos(t * 1.25) * sunPulse * 0.020, 1);
        data.sun.rotation.z += Math.sin(t * 0.32 + seed) * 0.010 * sunPulse;
      }
      // 歌词整体的慢速呼吸缩放。
      var breathe = Math.sin(t * 0.92 + seed) * 0.050 + Math.sin(t * 0.41 + seed * 0.7) * 0.028;
      if (skullMouthLyrics) {
        // 嘴部歌词在骷髅本地空间中轻微上下浮动。
        var mouthMeshY = -0.070 + Math.sin(t * 0.50 + seed) * 0.018 + Math.sin(t * 1.12 + seed) * 0.006;
        var mouthMeshZ = 0.018 + Math.cos(t * 0.46 + seed) * 0.007;
        var mouthMeshScale = 1.08 + a * 0.040 + breathe * 0.12 + bass * 0.024 + beatPulse * 0.014;
        if (!mesh.userData.skullMouthMeshLocked) {
          // 第一次进入嘴部布局时直接设置位置。
          mesh.position.set(0, mouthMeshY, mouthMeshZ);
          mesh.userData.skullMouthMeshLocked = true;
        } else {
          // 后续帧平滑跟随。
          mesh.position.x += (0 - mesh.position.x) * 0.18;
          mesh.position.y += (mouthMeshY - mesh.position.y) * 0.16;
          mesh.position.z += (mouthMeshZ - mesh.position.z) * 0.18;
        }
        mesh.scale.setScalar(mouthMeshScale);
        mesh.rotation.z = Math.sin(t * 0.30 + seed) * 0.010;
      } else {
        // 普通舞台歌词在封面前方漂浮。
        mesh.userData.skullMouthMeshLocked = false;
        mesh.scale.setScalar(0.96 + a * 0.055 + breathe + bass * 0.038 + beatPulse * 0.014);
        mesh.position.y += ((0.18 + Math.sin(t * 0.55 + seed) * 0.055 + Math.sin(t * 1.35 + seed) * 0.014) - mesh.position.y) * 0.075;
        mesh.position.z += ((1.48 + Math.cos(t * 0.48 + seed) * 0.080) - mesh.position.z) * 0.080;
        mesh.rotation.z = Math.sin(t * 0.34 + seed) * 0.018;
      }
      // 根据开关或残留透明度决定火花可见性。
      if (data.sparks && data.sparkMat) data.sparks.visible = fx.lyricGlowParticles || getLyricSparkOpacity(data) > 0.015;
      if (data.sparks && data.basePositions) {
        // 更新火花粒子的位置扰动。
        var pos = data.sparks.geometry.attributes.position;
        // 当前火花位置数组和原始位置数组。
        var arr = pos.array, base = data.basePositions;
        data.sparks.rotation.z += ((fx.lyricGlowParticles ? 0.0009 : 0.00025) + stageLyrics.beatGlow * 0.0007) * (dt * 60);
        data.sparks.rotation.x = Math.sin(t * 0.12 + seed) * 0.012;
        for (var si = 0; si < arr.length / 3; si++) {
          // 单粒子的稳定随机相位。
          var s = si * 12.989 + seed;
          // 粒子节拍和呼吸幅度。
          var particleBeat = fx.lyricGlowParticles ? stageLyrics.beatGlow : 0;
          var dustBreath = fx.lyricGlowParticles ? (0.62 + 0.38 * Math.sin(t * (0.32 + (si % 7) * 0.025) + s)) : 0.18;
          var drift = fx.lyricGlowParticles ? 1 : 0.30;
          arr[si*3] = base[si*3] + Math.sin(t * (0.18 + (si % 5) * 0.025) + s) * (0.045 + bass * 0.030 + particleBeat * 0.052) * drift + Math.cos(t * 0.11 + s) * 0.018 * dustBreath;
          arr[si*3+1] = base[si*3+1] + Math.cos(t * (0.16 + (si % 6) * 0.024) + s) * (0.042 + mid * 0.026 + particleBeat * 0.046) * drift + Math.sin(t * 0.13 + s) * 0.016 * dustBreath;
          arr[si*3+2] = base[si*3+2] + Math.sin(t * (0.24 + (si % 4) * 0.035) + s) * (0.036 + particleBeat * 0.028) * drift;
        }
        pos.needsUpdate = true;
      }
      return true;
    }
    // 淡出歌词透明度随退场曲线降低。
    opacity = (1 - a) * 0.72 * shelfDetailLyricProfile.outgoing;
    if (data.textMat) data.textMat.uniforms.uOpacity.value = opacity;
    if (data.readabilityMat) data.readabilityMat.opacity = opacity * (shelfDetailOpen ? shelfDetailLyricProfile.readability : 0.58);
    if (data.textMat && data.textMat.uniforms.uSolar) data.textMat.uniforms.uSolar.value *= shelfDetailOpen ? 0.72 : 0.86;
    if (data.glowMat) data.glowMat.opacity = lyricGlowStrength > 0 ? (shelfDetailOpen ? Math.min(shelfDetailLyricProfile.glowCap * 0.40, opacity * 0.05 * lyricGlowStrength) : opacity * 0.08 * lyricGlowStrength) : 0;
    if (data.sparkMat) {
      // 淡出歌词的火花快速消散。
      var outgoingSpark = lyricGlowStrength > 0 && fx.lyricGlowParticles && !shelfDetailOpen ? Math.max(opacity * 0.24 * lyricGlowStrength, (1 - a) * 0.18 * lyricGlowStrength) : 0;
      setLyricSparkOpacity(data, outgoingSpark);
      setLyricSparkSize(data, 0.046 + (1 - a) * 0.020);
    }
    if (data.sunMat) data.sunMat.opacity = lyricGlowStrength > 0 && !shelfDetailOpen ? opacity * 0.08 * lyricGlowStrength : 0;
    // 淡出歌词向后上方轻移。
    mesh.position.z -= dt * 0.26;
    mesh.position.y += dt * 0.08;
    mesh.scale.setScalar(0.98 - a * 0.06);
    return a < 1;
  }
  // 更新当前歌词。
  tickMesh(stageLyrics.current, true);
  // 逆序更新淡出队列，结束的 mesh 直接释放。
  for (var i = stageLyrics.outgoing.length - 1; i >= 0; i--) {
    if (!tickMesh(stageLyrics.outgoing[i], false)) {
      disposeLyricMesh(stageLyrics.outgoing[i]);
      stageLyrics.outgoing.splice(i, 1);
    }
  }
}

// 将宿主提供的逐字歌词时间数据归一化为内部格式。
function normalizeLyricCharacters(characters, timeScale) {
  // timeScale 为 ms 时需要除以 1000 转成秒。
  var scale = timeScale === 'ms' ? 1000 : 1;
  // offset 记录当前字符在整行文本中的起始位置。
  var offset = 0;
  // 输出逐字段数组。
  var output = [];
  (Array.isArray(characters) ? characters : []).forEach(function(character) {
    // 兼容 text/t 两种字段名。
    var text = String(character && (character.text != null ? character.text : character.t) || '');
    if (!text) return;
    // 兼容 startTime/endTime 和 s/e 字段名。
    var start = Number(character && (character.startTime != null ? character.startTime : character.s));
    var end = Number(character && (character.endTime != null ? character.endTime : character.e));
    if (!isFinite(start)) start = 0;
    if (!isFinite(end)) end = start;
    start = Math.max(0, start / scale);
    end = Math.max(start + 0.001, end / scale);
    // 当前片段覆盖的字符范围。
    var c0 = offset;
    offset += text.length;
    output.push({ text:text, t:start, d:Math.max(0.001, end - start), c0:c0, c1:offset });
  });
  return output;
}
// 读取歌词行中的有效逐字时间单元。
function lyricTimingUnits(line) {
  if (!line) return [];
  if (Array.isArray(line.characters) && line.characters.length > 1) return line.characters;
  return [];
}
// 判断歌词行是否有可用的逐字时间信息。
function hasValidLyricCharacters(line) {
  // 先取逐字时间单元。
  var units = lyricTimingUnits(line);
  // charCount 是整行字符总数，用于把字符位置映射到 0..1 进度。
  var count = line && Number(line.charCount) || 0;
  return units.length > 1 && count > 0 && units.some(function(unit){
    return unit && isFinite(unit.t) && isFinite(unit.d) && unit.d > 0 && unit.c1 > unit.c0;
  });
}
// 根据当前播放时间计算当前歌词行的卡拉 OK 高亮进度。
function getLyricLineProgress(line, nextLine, now) {
  // 没有逐字数据时返回 null，让 shader 不显示精确高亮。
  if (!line || !Array.isArray(line.characters) || line.characters.length <= 1) return null;
  if (!hasValidLyricCharacters(line)) return null;
  // 逐字时间单元。
  var units = lyricTimingUnits(line);
  // 轻微提前，让高亮视觉更贴近听感。
  now += 0.030;
  if (units.length && line.charCount > 0) {
    // lastP 记录已经完成到的最大进度。
    var lastP = 0;
    for (var i = 0; i < units.length; i++) {
      // 当前逐字段。
      var w = units[i];
      // 当前字段开始和结束时间。
      var ws = w.t;
      var we = w.t + Math.max(0.08, w.d || 0.24);
      if (now < ws) return lastP;
      // 当前字段内部进度。
      var local = now >= we ? 1 : (now - ws) / Math.max(0.08, we - ws);
      local = Math.max(0, Math.min(1, local));
      // 把字段内部进度映射到整行字符进度。
      var p = (w.c0 + (w.c1 - w.c0) * local) / line.charCount;
      lastP = Math.max(lastP, p);
      if (now < we) return lastP;
    }
    return 1;
  }
  return null;
}

// 根据播放时间同步舞台歌词行和逐字进度。
function tickLyricsParticles() {
  if (!fx.particleLyrics) {
    // 关闭舞台歌词时清理当前和淡出歌词。
    if (stageLyrics.current || stageLyrics.currentText || (stageLyrics.outgoing && stageLyrics.outgoing.length)) clearStageLyrics();
    return;
  }
  if (!audio || !lyricsLines.length) {
    // 没有音频或歌词时，把当前歌词转入淡出。
    if (stageLyrics.current) {
      stageLyrics.current.userData.state = 'out';
      stageLyrics.current.userData.age = 0;
      stageLyrics.outgoing.push(stageLyrics.current);
      stageLyrics.current = null;
      stageLyrics.currentIdx = -1;
      stageLyrics.currentText = '';
    }
    return;
  }
  // 当前播放时间。
  var t = audio.currentTime;
  // 基于本地音频时间搜索当前歌词行（参考 EchoMusic-Lyrics-WinIsland 时间驱动模式）。
  var newIdx = -1;
  for (var i = 0; i < lyricsLines.length; i++) {
    if (lyricsLines[i].t <= t + 0.05) newIdx = i; else break;
  }
  if (newIdx < 0) {
    // 播放时间还没到第一句时清空舞台歌词。
    clearStageLyrics();
    return;
  }
  if (newIdx !== stageLyrics.currentIdx) {
    // 切换到新歌词行。
    stageLyrics.currentIdx = newIdx;
    showStageLine(lyricsLines[newIdx].text || '');
  }
  if (stageLyrics.current) {
    // 根据当前行逐字信息更新 shader 进度。
    var curLine = lyricsLines[newIdx] || { t:t };
    var nextLine = lyricsLines[newIdx + 1];
    var progress = getLyricLineProgress(curLine, nextLine, t);
    updateLyricMeshProgress(stageLyrics.current, progress);
  }
}

// 销毁舞台歌词系统的所有 Three.js 对象。
function disposeLyricsParticles() {
  // 先清理当前歌词和淡出歌词。
  clearStageLyrics();
  if (stageLyrics.starRiver) {
    // 星河粒子有独立几何和材质，需要释放。
    if (stageLyrics.starRiver.parent) stageLyrics.starRiver.parent.remove(stageLyrics.starRiver);
    if (stageLyrics.starRiver.geometry) stageLyrics.starRiver.geometry.dispose();
    if (stageLyrics.starRiver.material) stageLyrics.starRiver.material.dispose();
    stageLyrics.starRiver = null;
  }
  if (stageLyrics.group) {
    // 移除歌词总分组。
    scene.remove(stageLyrics.group);
    stageLyrics.group = null;
  }
}


// ===== js/04-visual-analysis-beat.js =====

// ============================================================
//  涟漪触发系统 — 3×3 九宫格 + bass 上升沿
// ============================================================
// 下一个要复用的涟漪槽位索引。
var rippleIdx = 0;
// 上一次触发涟漪的时间。
var lastRippleAt = 0;
// 上一帧低频是否处于上升沿状态。
var lastBassRising = false;
// 触发低频涟漪的阈值。
var BASS_THRESHOLD = 0.30;
// 涟漪触发冷却时间，避免低频连续抖动生成过多涟漪。
var RIPPLE_COOLDOWN = 0.32;

// 九宫格涟漪候选区域。
var regions = [];
// 按 3×3 网格生成平面上的候选中心点。
for (var ry = 0; ry < 3; ry++) for (var rx = 0; rx < 3; rx++) {
  regions.push({
    x: (rx / 2 - 0.5) * PLANE_SIZE * 0.72,
    y: (ry / 2 - 0.5) * PLANE_SIZE * 0.72,
  });
}

// 在指定坐标触发一个涟漪。
function triggerRipple(x, y, strength) {
  // 复用当前槽位对象。
  var r = ripples[rippleIdx];
  // 重置涟漪位置、年龄和强度。
  r.x = x; r.y = y; r.age = 0; r.str = strength;
  // 环形推进槽位索引。
  rippleIdx = (rippleIdx + 1) % RIPPLE_MAX;
}

// 更新涟漪生命周期，并把数据写入 DataTexture。
function updateRipples(dt) {
  // 低频从阈值下方跨过阈值时触发一次涟漪。
  var isBassHit = bass > BASS_THRESHOLD && !lastBassRising;
  // 使用较低阈值释放上升沿锁定，形成迟滞。
  lastBassRising = bass > BASS_THRESHOLD * 0.75;
  // 使用 shader 时间作为涟漪触发时间基准。
  var now = uniforms.uTime.value;
  if (isBassHit && (now - lastRippleAt) > RIPPLE_COOLDOWN) {
    // 记录触发时间并随机触发 2 到 3 个区域。
    lastRippleAt = now;
    var count = 2 + (Math.random() < 0.5 ? 0 : 1);
    // 本次触发已使用的九宫格区域。
    var used = {};
    for (var k = 0; k < count; k++) {
      // 随机挑一个尽量未使用的区域。
      var idx, tries = 0;
      do { idx = Math.floor(Math.random() * 9); tries++; } while (used[idx] && tries < 12);
      used[idx] = true;
      // 区域中心加一点随机偏移，避免每次位置完全相同。
      var reg = regions[idx];
      var jx = reg.x + (Math.random() - 0.5) * 0.7;
      var jy = reg.y + (Math.random() - 0.5) * 0.7;
      var str = 0.65 + bass * 1.4 + Math.random() * 0.25;
      triggerRipple(jx, jy, str);
    }
  }

  for (var i = 0; i < RIPPLE_MAX; i++) {
    // 更新每个涟漪槽位的生命周期。
    var r = ripples[i];
    if (r.str > 0.005) {
      r.age += dt;
      if (r.age > 2.0) { r.str = 0; r.age = -10; }
    }
    // 每个涟漪写入四个通道：x、y、age、strength。
    var off = i * 4;
    rippleData[off]   = r.x;
    rippleData[off+1] = r.y;
    rippleData[off+2] = r.age;
    rippleData[off+3] = r.str;
  }
  // 通知 Three.js 上传新的 DataTexture。
  rippleTex.needsUpdate = true;

  // 统计当前仍有效的涟漪数量。
  var active = 0;
  for (var i = 0; i < RIPPLE_MAX; i++) if (ripples[i].str > 0.005) active++;
  uniforms.uRippleCount.value = active;
}

// ============================================================
//  封面 + 边缘 + 启发式深度 处理 (CPU 端)
//   生成 256×256 RGBA 纹理: R=depth G=edge B=fg-mask A=lum
// ============================================================
function coverDepthCacheId(raw) {
  // 从封面 URL 或缓存键中提取文件名（不含后缀）作为 hash。
  var str = String(raw || '')
  if (!str) return ''
  // 去掉 |tex=NxN 尺寸后缀
  var pure = str.split('|')[0]
  // 取最后一段作为文件名
  var name = pure.split('/').pop()
  if (!name) return ''
  // 去掉扩展名
  var dot = name.lastIndexOf('.')
  return dot > 0 ? name.slice(0, dot) : name
}

function buildEdgeAndDepth(srcCanvas) {
  // CPU 端从封面生成四通道辅助纹理：R=深度，G=边缘，B=前景遮罩，A=亮度。
  // shader 后续用这张纹理做粒子位移、边缘提亮和封面前景层次，不需要每帧重复分析图片。
  // 输出尺寸和像素总数。
  var W = 256, H = 256, N = W * H;
  // 先把任意尺寸封面规整到 256×256。
  var normalized = document.createElement('canvas');
  normalized.width = W;
  normalized.height = H;
  var sctx = normalized.getContext('2d');
  sctx.drawImage(srcCanvas, 0, 0, W, H);
  // 读取规整后的像素。
  var src = sctx.getImageData(0, 0, W, H).data;
  // 亮度、模糊结果和临时缓冲。
  var lum = new Float32Array(N), blur = new Float32Array(N), tmp = new Float32Array(N);
  // 1) Luminance
  for (var i = 0; i < N; i++) {
    var di = i * 4;
    lum[i] = (src[di] * 0.299 + src[di+1] * 0.587 + src[di+2] * 0.114) / 255;
  }
  // 2) Box blur 2 次 (深度基础)
  // 横向盒模糊。
  function blurH(s, d, r) {
    for (var y = 0; y < H; y++) {
      var sum = 0;
      for (var x = -r; x <= r; x++) sum += s[y * W + Math.max(0, Math.min(W-1, x))];
      for (var x = 0; x < W; x++) {
        d[y * W + x] = sum / (2*r + 1);
        var xR = Math.min(W-1, x + r + 1), xL = Math.max(0, x - r);
        sum += s[y * W + xR] - s[y * W + xL];
      }
    }
  }
  // 纵向盒模糊。
  function blurV(s, d, r) {
    for (var x = 0; x < W; x++) {
      var sum = 0;
      for (var y = -r; y <= r; y++) sum += s[Math.max(0, Math.min(H-1, y)) * W + x];
      for (var y = 0; y < H; y++) {
        d[y * W + x] = sum / (2*r + 1);
        var yD = Math.min(H-1, y + r + 1), yU = Math.max(0, y - r);
        sum += s[yD * W + x] - s[yU * W + x];
      }
    }
  }
  blurH(lum, tmp, 4); blurV(tmp, blur, 4);

  // 3) Sobel 边缘 (在 blur 上做 - 减少噪声)
  // edge 保存 Sobel 边缘强度。
  var edge = new Float32Array(N);
  for (var y = 1; y < H-1; y++) for (var x = 1; x < W-1; x++) {
    var gx = -blur[(y-1)*W + (x-1)] - 2*blur[y*W + (x-1)] - blur[(y+1)*W + (x-1)]
            + blur[(y-1)*W + (x+1)] + 2*blur[y*W + (x+1)] + blur[(y+1)*W + (x+1)];
    var gy = -blur[(y-1)*W + (x-1)] - 2*blur[(y-1)*W + x] - blur[(y-1)*W + (x+1)]
            + blur[(y+1)*W + (x-1)] + 2*blur[(y+1)*W + x] + blur[(y+1)*W + (x+1)];
    edge[y*W + x] = Math.min(1.0, Math.sqrt(gx*gx + gy*gy) * 1.4);
  }
  // 4) 启发式深度:亮度 + 中心 mask + 边缘累积
  // depth 保存启发式景深。
  var depth = new Float32Array(N);
  for (var y = 0; y < H; y++) for (var x = 0; x < W; x++) {
    var i = y*W + x;
    // 归一化到中心为 0 的坐标。
    var cx = (x / (W-1) - 0.5) * 2.0;
    var cy = (y / (H-1) - 0.5) * 2.0;
    var rr = Math.sqrt(cx*cx + cy*cy);
    var centerBias = 1.0 - Math.min(1, rr * 0.75);
    var bright = blur[i];
    depth[i] = Math.min(1.0, bright * 0.45 + centerBias * 0.55);
  }
  // 5) fg-mask: 中心 + 高对比区
  // fg 前景遮罩由深度和边缘混合得到。
  var fg = new Float32Array(N);
  for (var i = 0; i < N; i++) {
    var d = depth[i];
    var e = edge[i];
    fg[i] = Math.min(1.0, d * 0.6 + e * 0.5);
  }

  // 输出 256×256 RGBA
  // 创建输出 canvas 和 ImageData。
  var out = document.createElement('canvas'); out.width = W; out.height = H;
  var octx = out.getContext('2d'), imgOut = octx.createImageData(W, H);
  for (var i = 0; i < N; i++) {
    var di = i * 4;
    imgOut.data[di]   = Math.round(depth[i] * 255);
    imgOut.data[di+1] = Math.round(edge[i] * 255);
    imgOut.data[di+2] = Math.round(fg[i] * 255);
    imgOut.data[di+3] = Math.round(lum[i] * 255);
  }
  octx.putImageData(imgOut, 0, 0);
  return out;
}

// AI 深度估计 (Xenova/depth-anything-small) - 异步加载, 失败回退
async function ensureAIDepthPipeline() {
  // AI 深度模型按需懒加载；失败时保持启发式深度可用，避免封面切换链路被模型加载阻断。
  if (aiDepthReady && aiDepthPipeline) return aiDepthPipeline;
  // 已有加载任务时不并发启动第二个模型加载。
  if (aiDepthBusy) return null;
  aiDepthBusy = true;
  try {
    // 首次加载会下载模型，UI 上显示短提示。
    showAIDepthChip('加载 AI 深度模型 (首次需下载 50MB)…');
    // 从 CDN 动态导入 transformers.js。
    var mod = await import('./vendor/transformers.min.js');
    // 禁用本地模型查找，直接走远端资源。
    mod.env.allowLocalModels = false;
    // 限制 wasm 线程，降低播放器内嵌环境压力。
    if (mod.env.backends && mod.env.backends.onnx && mod.env.backends.onnx.wasm) mod.env.backends.onnx.wasm.numThreads = 1;
    // 创建深度估计 pipeline。
    aiDepthPipeline = await mod.pipeline('depth-estimation', 'Xenova/depth-anything-small-hf');
    aiDepthReady = true;
    return aiDepthPipeline;
  } catch (e) {
    // 加载失败时只记录警告，封面仍使用启发式深度。
    console.warn('AI depth pipeline failed:', e);
    return null;
  } finally {
    aiDepthBusy = false;
  }
}

// 为 AI 深度估计生成较小的输入 canvas。
function makeAIDepthInputCanvas(srcCanvas) {
  // 没有源 canvas 时直接返回。
  if (!srcCanvas) return srcCanvas;
  // 小尺寸输入可显著降低模型推理耗时。
  var size = 160;
  // 规整输入 canvas。
  var cv = document.createElement('canvas');
  cv.width = cv.height = size;
  var ctx = cv.getContext('2d');
  try {
    // 把源封面缩放绘制到 160×160。
    ctx.drawImage(srcCanvas, 0, 0, size, size);
    return cv;
  } catch (e) {
    return srcCanvas;
  }
}

// 使用 AI 模型估计封面深度图。
async function estimateAIDepth(srcCanvas, token) {
  // token 在模型加载前后都要校验，防止上一张封面的异步结果覆盖当前封面。
  if (!fx.aiDepth) return null;
  // 近期失败后进入冷却，避免频繁重试。
  if (performance.now() < aiDepthFailUntil) return null;
  showAIDepthChip('后台增强封面深度…');
  try {
    // 确保模型 pipeline 可用。
    var pipe = await ensureAIDepthPipeline();
    if (!pipe) { hideAIDepthChip(); return null; }
    if (token !== coverProcessToken) { hideAIDepthChip(); return null; }
    // 缩小输入尺寸。
    var inputCanvas = makeAIDepthInputCanvas(srcCanvas);
    // transformers.js 可以接受 data URL，优先转成 JPEG 字符串。
    var input = inputCanvas;
    try {
      if (inputCanvas && inputCanvas.toDataURL) input = inputCanvas.toDataURL('image/jpeg', 0.82);
    } catch (e) {
      input = inputCanvas;
    }
    // 执行推理。
    var result = await pipe(input);
    if (token !== coverProcessToken) { hideAIDepthChip(); return null; }
    // 兼容不同返回字段。
    var raw = result && (result.depth || result.predicted_depth || result);
    var rawCv = raw && raw.toCanvas ? await raw.toCanvas() : raw;
    hideAIDepthChip();
    return rawCv;
  } catch (e) {
    // 推理失败后冷却两分钟，再回退启发式深度。
    console.warn('AI depth estimation failed:', e);
    aiDepthFailUntil = performance.now() + 120000;
    hideAIDepthChip();
    return null;
  }
}

function mergeAIDepthIntoEdgeTexture(heuristicCanvas, aiCanvas) {
  // 把 AI 深度 (灰度) 写入 R 通道, 保留启发式的 G/B/A
  // 只替换 R 通道是为了复用启发式边缘和前景遮罩，AI 结果只承担更准确的景深层次。
  // 输出纹理尺寸。
  var W = heuristicCanvas.width || 256, H = heuristicCanvas.height || 256;
  // 读取启发式纹理。
  var hctx = heuristicCanvas.getContext('2d');
  var hImg = hctx.getImageData(0, 0, W, H);

  // 把 AI 深度图缩放到启发式纹理尺寸。
  var aiTmp = document.createElement('canvas'); aiTmp.width = W; aiTmp.height = H;
  var actx = aiTmp.getContext('2d');
  actx.drawImage(aiCanvas, 0, 0, W, H);
  var aData = actx.getImageData(0, 0, W, H).data;

  // 归一化 AI 深度
  // aiVals 保存灰度深度值，min/max 用于归一化。
  var aiVals = new Float32Array(W * H), minV = 1, maxV = 0;
  for (var i = 0; i < aiVals.length; i++) {
    var di = i * 4;
    var v = (aData[di] * 0.299 + aData[di+1] * 0.587 + aData[di+2] * 0.114) / 255;
    aiVals[i] = v; if (v < minV) minV = v; if (v > maxV) maxV = v;
  }
  // 深度取值范围，避免除零。
  var range = Math.max(0.001, maxV - minV);
  // 判断是否反相 (中心应该比边缘深, 表示前景在中)
  // 分别统计中心区域和边缘区域平均深度。
  var centerSum = 0, centerCount = 0, edgeSum = 0, edgeCount = 0;
  for (var y = 0; y < H; y++) for (var x = 0; x < W; x++) {
    var i = y * W + x;
    var cx = x / (W-1) - 0.5, cy = y / (H-1) - 0.5;
    var rr = Math.sqrt(cx*cx + cy*cy);
    if (rr < 0.22) { centerSum += aiVals[i]; centerCount++; }
    else if (rr > 0.46) { edgeSum += aiVals[i]; edgeCount++; }
  }
  var invert = (centerSum / Math.max(1, centerCount)) < (edgeSum / Math.max(1, edgeCount));

  for (var i = 0; i < aiVals.length; i++) {
    // 归一化深度并按需要反相。
    var n = (aiVals[i] - minV) / range;
    if (invert) n = 1.0 - n;
    hImg.data[i*4] = Math.round(n * 255);
  }
  hctx.putImageData(hImg, 0, 0);
  return heuristicCanvas;
}

function queueAIDepthForCover(srcCanvas, edgeCanvas, token, opts, cacheSeed, force) {
  // AI 增强排到空闲时段执行，并在每个等待点检查 token 和封面来源，避免后台任务抢占交互帧。
  opts = opts || {};
  // 缺少开关或输入时不排队。
  if (!fx.aiDepth || !srcCanvas || !edgeCanvas) return;
  // 后台优化释放资源时不启动非强制 AI 任务。
  if (!force && isHiddenForBackgroundOptimization()) return;
  // 模型失败冷却或忙碌中直接跳过。
  if (performance.now() < aiDepthFailUntil || aiDepthBusy) return;
  // 限制非强制 AI 深度任务频率。
  var now = performance.now();
  if (!force && now - aiDepthLastRunAt < aiDepthMinGapMs) return;
  aiDepthLastRunAt = now;
  scheduleVisualApply(async function(){
    // 所有异步阶段都校验 token 和封面来源。
    if (!fx.aiDepth || token !== coverProcessToken || !coverApplyStillCurrent(opts)) return;
    await yieldToIdle(force ? 900 : 2600);
    if (!fx.aiDepth || token !== coverProcessToken || !coverApplyStillCurrent(opts)) return;
    // 推理成功后合并到当前 edgeCanvas。
    var aiCanvas = await estimateAIDepth(srcCanvas, token);
    if (!aiCanvas || token !== coverProcessToken || !coverApplyStillCurrent(opts)) return;
    mergeAIDepthIntoEdgeTexture(edgeCanvas, aiCanvas);
    coverEdgeTex.image = edgeCanvas;
    coverEdgeTex.needsUpdate = true;
    // 更新深度状态和缓存。
    setCoverDepthState(1, 1.0, 360);
    (async function(){
      var hash = coverDepthCacheId(cacheSeed);
      var dataUrl = edgeCanvas.toDataURL();
      console.log('[深度缓存] 写入 AI 深度:', { hash: hash, id: cacheSeed, width: edgeCanvas.width, height: edgeCanvas.height, dataUrl: dataUrl, timestamp: Date.now() });
      await putDepthToIDB(hash, dataUrl, edgeCanvas.width, edgeCanvas.height);
    })();
    showToast('AI 深度已后台增强');
  }, force ? 240 : 1800, force ? 1200 : 3000);
}

// 对当前封面强制排队一次 AI 深度增强。
function queueAIDepthForCurrentCover(force) {
  // 当前封面或深度纹理不可用时跳过。
  if (!coverTex || !coverTex.image || !coverEdgeTex || !coverEdgeTex.image) return;
  if (!uniforms.uHasCover.value || !uniforms.uHasDepth.value) return;
  queueAIDepthForCover(coverTex.image, coverEdgeTex.image, coverProcessToken, {}, '', !!force);
}

// 颜色渐变 tween (切歌时旧封面→新封面)
// 当前封面颜色混合动画句柄。
var colorMixTween = null;
// 启动新旧封面颜色混合动画。
function startColorMixTween(durationMs) {
  // 取消上一轮混合动画。
  if (colorMixTween) cancelAnimationFrame(colorMixTween.raf);
  // 动画时长至少 1ms。
  durationMs = Math.max(1, durationMs || 1);
  // 记录起点时间。
  var start = performance.now();
  // 从旧封面开始混合。
  uniforms.uColorMixT.value = 0;
  // requestAnimationFrame 步进函数。
  function step(now) {
    // 计算 0..1 进度。
    var t = Math.min(1, (now - start) / durationMs);
    // 使用视觉缓动曲线。
    t = visualEase(t);
    uniforms.uColorMixT.value = t;
    if (t < 1) colorMixTween = { raf: requestAnimationFrame(step) };
    else colorMixTween = null;
  }
  colorMixTween = { raf: requestAnimationFrame(step) };
}

// 粒子整体透明度 tween (启动 fade-in)
// 主粒子透明度动画句柄。
var alphaTween = null;
// 浮空粒子透明度动画句柄。
var floatAlphaTween = null;
// 空闲粒子目标透明度，当前默认关闭。
var IDLE_PARTICLE_ALPHA = 0;
// 缓动主粒子整体透明度。
function tweenParticleAlpha(from, to, durationMs) {
  // 取消上一轮透明度动画。
  if (alphaTween) cancelAnimationFrame(alphaTween.raf);
  // 记录起点时间。
  var start = performance.now();
  // requestAnimationFrame 步进函数。
  function step(now) {
    // smoothstep 进度。
    var t = Math.min(1, (now - start) / durationMs);
    t = t * t * (3 - 2 * t);
    uniforms.uAlpha.value = from + (to - from) * t;
    if (t < 1) alphaTween = { raf: requestAnimationFrame(step) };
    else alphaTween = null;
  }
  alphaTween = { raf: requestAnimationFrame(step) };
}
// 缓动浮空粒子透明度。
function tweenFloatAlpha(from, to, durationMs) {
  // 取消上一轮浮空透明度动画。
  if (floatAlphaTween) cancelAnimationFrame(floatAlphaTween.raf);
  // 记录起点时间。
  var start = performance.now();
  function step(now) {
    var t = Math.min(1, (now - start) / durationMs);
    t = t * t * (3 - 2 * t);
    uniforms.uFloatAlpha.value = from + (to - from) * t;
    if (t < 1) floatAlphaTween = { raf: requestAnimationFrame(step) };
    else floatAlphaTween = null;
  }
  floatAlphaTween = { raf: requestAnimationFrame(step) };
}
// 显示空闲粒子；当前版本会清空浮空层并保持透明。
function revealIdleParticles(target, durationMs) {
  // uniform 不存在时跳过。
  if (!uniforms || !uniforms.uFloatAlpha) return;
  // 取消浮空透明度动画并归零。
  if (floatAlphaTween) { cancelAnimationFrame(floatAlphaTween.raf); floatAlphaTween = null; }
  uniforms.uFloatAlpha.value = 0;
  if (floatGroup) destroyFloatLayer();
}
// 显示用户选择的视觉预设粒子层。
function revealUserPresetParticles(opts) {
  // opts 支持 instant、alpha、duration 等控制。
  opts = opts || {};
  if (!uniforms || !uniforms.uAlpha) return;
  // 用户预设出现时关闭浮空层。
  if (uniforms.uFloatAlpha) uniforms.uFloatAlpha.value = 0;
  if (floatGroup) destroyFloatLayer();
  if (typeof syncFxUniforms === 'function') syncFxUniforms();
  if (typeof SKULL_PRESET_INDEX !== 'undefined' && fx && fx.preset === SKULL_PRESET_INDEX && typeof loadSkullParticleAsset === 'function') {
    // 骷髅预设提前加载点云资源。
    loadSkullParticleAsset();
  }
  // 主粒子目标透明度。
  var target = typeof opts.alpha === 'number' ? opts.alpha : 0.96;
  // 当前透明度。
  var current = uniforms.uAlpha.value || 0;
  if (opts.instant) {
    // instant 模式直接设置目标透明度。
    if (alphaTween) { cancelAnimationFrame(alphaTween.raf); alphaTween = null; }
    uniforms.uAlpha.value = target;
    return;
  }
  if (current < target - 0.01) tweenParticleAlpha(current, target, opts.duration || 920);
}

// 加载形态 tween (uLoading 0..1)
// 加载动画句柄。
var loadingTween = null;
// 加载态显示开始时间。
var loadingShownAt = 0;
// 加载态延迟隐藏定时器，用于避免封面快速切换时 loading 闪烁。
var loadingHideTimer = null;
// 封面深度与 AI 增强强度的补间动画句柄。
var coverDepthTween = null;
// 视觉补间通用缓动函数，把线性进度压成平滑的 0..1 曲线。
function visualEase(t) {
  // 先把进度夹在合法区间内，避免动画超界导致 uniform 数值漂移。
  t = Math.max(0, Math.min(1, t));
  // smoothstep 曲线，起止速度为 0，适合 loading 和深度状态的短动画。
  return t * t * (3 - 2 * t);
}
// 将粒子材质的加载态 uniform 补间到指定值。
function tweenLoading(to, durationMs, onComplete) {
  // 新 loading 动画开始前取消旧帧，保证同一时间只有一个补间写 uLoading。
  if (loadingTween) cancelAnimationFrame(loadingTween.raf);
  // 最小持续时间为 1ms，避免除以 0。
  durationMs = Math.max(1, durationMs || 1);
  // 后台省电或深度后台模式不跑动画，直接落到目标值并回调。
  if (isHiddenForBackgroundOptimization() || isDeepBackgroundMode()) {
    uniforms.uLoading.value = to;
    loadingTween = null;
    if (onComplete) onComplete();
    return;
  }
  // 记录补间起点时间和值，后续帧只根据时间差推进。
  var start = performance.now();
  var from = uniforms.uLoading.value;
  // requestAnimationFrame 驱动的逐帧补间逻辑。
  function step(now) {
    // 当前帧归一化进度。
    var t = Math.min(1, (now - start) / durationMs);
    // 平滑后的进度。
    var eased = visualEase(t);
    // 根据起点和目标值写入 loading 强度。
    uniforms.uLoading.value = from + (to - from) * eased;
    if (t < 1) loadingTween = { raf: requestAnimationFrame(step) };
    else {
      // 结束帧强制对齐目标值，消除浮点误差。
      uniforms.uLoading.value = to;
      loadingTween = null;
      if (onComplete) onComplete();
    }
  }
  // 保存动画帧句柄，便于后续封面切换或后台恢复时取消。
  loadingTween = { raf: requestAnimationFrame(step) };
}
// 隐藏封面加载态，并保留极短最小显示时间减少闪烁。
function hideLoading() {
  // 重复调用时重置上一次延迟隐藏任务。
  if (loadingHideTimer) clearTimeout(loadingHideTimer);
  // 后台场景直接收敛 loading，不再排队动画。
  if (isHiddenForBackgroundOptimization() || isDeepBackgroundMode()) {
    forceLoadingSettled('background-hide');
    return;
  }
  // 计算 loading 已显示多久，至少显示约一帧以上再隐藏。
  var elapsed = loadingShownAt ? performance.now() - loadingShownAt : 999;
  // 短等待用于防止封面刚开始加载就结束时出现肉眼可见闪动。
  var wait = Math.max(0, 72 - elapsed);
  loadingHideTimer = setTimeout(function(){
    loadingHideTimer = null;
    // 根据当前 loading 强度决定是否需要补间淡出。
    var current = uniforms.uLoading.value || 0;
    if (current <= 0.015 || isHiddenForBackgroundOptimization() || isDeepBackgroundMode()) {
      // 已经接近 0 或进入后台时，取消补间并直接清零。
      if (loadingTween) {
        cancelAnimationFrame(loadingTween.raf);
        loadingTween = null;
      }
      uniforms.uLoading.value = 0;
      return;
    }
    // loading 越明显，淡出时间略长，避免突然跳变。
    tweenLoading(0, current > 0.38 ? 126 : 96);
  }, wait);
}
// 强制让加载态进入稳定关闭状态，通常用于后台恢复或异常收尾。
function forceLoadingSettled(reason) {
  // 清理延迟隐藏定时器。
  if (loadingHideTimer) {
    clearTimeout(loadingHideTimer);
    loadingHideTimer = null;
  }
  // 清理正在进行的 loading 补间。
  if (loadingTween) {
    cancelAnimationFrame(loadingTween.raf);
    loadingTween = null;
  }
  // 直接关闭 shader loading 状态并重置显示起点。
  uniforms.uLoading.value = 0;
  loadingShownAt = 0;
  // 调试开关开启时输出收敛原因，默认不影响控制台。
  if (reason && window.__mineradioDebugLoading) console.log('[LoadingSettled]', reason);
}
// 页面从后台或省电状态恢复后，修复渲染器、视口与 loading 残留状态。
function recoverVisualsAfterBackground(reason) {
  // 重新按当前可见性和性能策略应用渲染功耗模式。
  applyRendererPowerMode();
  // 如果主渲染视口刷新函数已经加载，则请求一次恢复刷新。
  if (typeof scheduleMainRendererViewportRefresh === 'function') scheduleMainRendererViewportRefresh(reason || 'restore');
  // 播放中恢复时，如果 loading 仍挂起，直接收敛，避免画面卡在加载形态。
  if (audio && audio.src && !audio.paused && ((uniforms.uLoading.value || 0) > 0.015 || loadingTween || loadingHideTimer)) {
    forceLoadingSettled(reason || 'restore');
  }
  // 背景恢复视为一次交互窗口，短时间提高渲染响应。
  if (typeof markRenderInteraction === 'function') markRenderInteraction('restore', 1100);
}

// 平滑切换封面深度贴图有效性和 AI 深度增强强度。
function setCoverDepthState(depthTo, aiTo, durationMs) {
  // 目标值统一夹在 0..1，避免外部调用传入异常数值。
  depthTo = Math.max(0, Math.min(1, Number(depthTo) || 0));
  aiTo = Math.max(0, Math.min(1, Number(aiTo) || 0));
  // 新的深度状态动画开始前取消旧动画。
  if (coverDepthTween) {
    cancelAnimationFrame(coverDepthTween.raf);
    coverDepthTween = null;
  }
  // 标准化动画时长。
  durationMs = Math.max(1, durationMs || 1);
  // 记录当前 shader 中的深度和 AI 增强强度。
  var depthFrom = uniforms.uHasDepth.value || 0;
  var aiFrom = uniforms.uAiBoost.value || 0;
  // 极短动画或目标几乎未变时直接写入，避免无意义 RAF。
  if (durationMs <= 1 || (Math.abs(depthFrom - depthTo) < 0.001 && Math.abs(aiFrom - aiTo) < 0.001)) {
    uniforms.uHasDepth.value = depthTo;
    uniforms.uAiBoost.value = aiTo;
    return;
  }
  // 记录动画起点时间。
  var start = performance.now();
  // 逐帧推进深度状态补间。
  function step(now) {
    // 当前补间进度。
    var t = Math.min(1, (now - start) / durationMs);
    // 平滑后的补间进度。
    var eased = visualEase(t);
    // 同步写入普通深度和 AI 增强两个 uniform。
    uniforms.uHasDepth.value = depthFrom + (depthTo - depthFrom) * eased;
    uniforms.uAiBoost.value = aiFrom + (aiTo - aiFrom) * eased;
    if (t < 1) coverDepthTween = { raf: requestAnimationFrame(step) };
    else {
      // 结束帧强制对齐目标值并释放句柄。
      uniforms.uHasDepth.value = depthTo;
      uniforms.uAiBoost.value = aiTo;
      coverDepthTween = null;
    }
  }
  // 保存 RAF 句柄，供后续封面切换取消。
  coverDepthTween = { raf: requestAnimationFrame(step) };
}

// 判断当前封面处理任务是否仍对应最新曲目，防止异步加载串歌。
function coverApplyStillCurrent(opts) {
  opts = opts || {};
  return !opts.trackToken || opts.trackToken === trackSwitchToken;
}

// 更新底部控制条中的封面缩略图背景。
function setControlCoverSrc(src) {
  // 控制条封面节点可能在不同布局下不存在。
  var cover = document.getElementById('control-cover');
  if (!cover) return;
  if (!src) {
    // 无封面时清空背景并标记为空态。
    cover.style.backgroundImage = '';
    cover.classList.add('cover-empty');
    return;
  }
  // 作为 CSS url 写入时转义双引号，避免路径中引号破坏样式。
  cover.style.backgroundImage = 'url("' + String(src).replace(/"/g, '\\"') + '")';
  cover.classList.remove('cover-empty');
}

// 更新底部控制条中的曲名和歌手。
function updateControlTrackInfo(song) {
  song = song || {};
  // 曲名文本节点。
  var title = document.getElementById('control-title');
  // 歌手文本节点。
  var artist = document.getElementById('control-artist');
  if (title) title.textContent = song.name || '';
  if (artist) artist.textContent = song.artist || '';
}

// 把已经解码并缩放好的封面 canvas 应用到主粒子材质、UI 缩略图和相关缓存。
function applyCoverCanvas(cv, thumbSrc, opts) {
  opts = opts || {};
  if (!cv || !coverApplyStillCurrent(opts)) return;
  var token = ++coverProcessToken;
  if (opts.coverSource && opts.coverSourceKind) {
    currentCoverSource = { kind: opts.coverSourceKind, src: opts.coverSource };
  }
  var cacheSeed = (opts.coverKey || thumbSrc || '') + '|tex=' + (cv.width || 0) + 'x' + (cv.height || 0);

  if (uniforms.uHasCover.value > 0.5 && coverTex.image) {
    var prevW = coverTex.image.width || 256;
    var prevH = coverTex.image.height || 256;
    var prevScale = Math.min(1, 256 / Math.max(prevW, prevH, 1));
    var prevCv = document.createElement('canvas');
    prevCv.width = Math.max(1, Math.round(prevW * prevScale));
    prevCv.height = Math.max(1, Math.round(prevH * prevScale));
    try {
      prevCv.getContext('2d').drawImage(coverTex.image, 0, 0, prevCv.width, prevCv.height);
      prevCoverTex.image = prevCv;
      prevCoverTex.needsUpdate = true;
    } catch (e) {}
  }
  coverTex.image = cv; coverTex.needsUpdate = true;
  coverPickerCanvas = cv;
  uniforms.uHasCover.value = 1;
  // 初始状态设为平面，等待异步深度缓存或启发式生成
  setCoverDepthState(0, 0, opts.deferHeavy ? 120 : 1);

  if (thumbSrc) {
    document.getElementById('thumb-cover').src = thumbSrc;
    setControlCoverSrc(thumbSrc);
  }
  if (shelfManager) shelfManager.onCoverChange(thumbSrc);

  var colorMixMs = opts.colorMixDuration || (fx.preset === 0 ? 520 : 1400);
  startColorMixTween(opts.fromResolutionChange ? (fx.preset === 0 ? 300 : 520) : colorMixMs);

  function refreshCoverDependentColors() {
    if (token !== coverProcessToken || !coverApplyStillCurrent(opts)) return;
    if (floatGroup) refreshFloatColorsFromCover(cv);
    if (backCoverGroup) refreshBackCoverColorsFromCanvas(cv);
    updateLyricPaletteFromCover(cv);
  }

  function runHeavyCoverWork() {
    if (token !== coverProcessToken || !coverApplyStillCurrent(opts)) return;
    if (opts.deferHeavy && typeof isRenderInteractionActive === 'function' && isRenderInteractionActive()) {
      scheduleVisualApply(runHeavyCoverWork, 420, 1800);
      return;
    }
    var edgeCv = buildEdgeAndDepth(cv);
    if (token !== coverProcessToken || !coverApplyStillCurrent(opts)) return;
    coverEdgeTex.image = edgeCv; coverEdgeTex.needsUpdate = true;
    refreshCoverDependentColors();
    queueAIDepthForCover(cv, edgeCv, token, opts, cacheSeed, false);
  }

  // 从 IndexedDB 异步加载深度缓存
  (async function(){
    var hash = coverDepthCacheId(cacheSeed)
    var cachedDepth = await getDepthFromIDB(hash)
    if (token !== coverProcessToken || !coverApplyStillCurrent(opts)) return
    if (cachedDepth && cachedDepth.dataUrl && cachedDepth.width && cachedDepth.height) {
      var img = new Image()
      img.src = cachedDepth.dataUrl
      await new Promise(function(resolve){ img.onload = resolve; img.onerror = resolve })
      if (token !== coverProcessToken || !coverApplyStillCurrent(opts)) return
      var edgeCv = document.createElement('canvas')
      edgeCv.width = cachedDepth.width
      edgeCv.height = cachedDepth.height
      edgeCv.getContext('2d').drawImage(img, 0, 0)
      coverEdgeTex.image = edgeCv
      coverEdgeTex.needsUpdate = true
      // 所有 IDB 条目均为 AI 深度，直接激活立体效果
      setCoverDepthState(1, 1.0, opts.deferHeavy ? 180 : 120)
      scheduleVisualApply(refreshCoverDependentColors, opts.deferHeavy ? 260 : 90, opts.deferHeavy ? 1200 : 700)
      return
    }
    var heavyDelay = opts.deferHeavy ? (opts.delay || 620) : (opts.delay || 120)
    var heavyTimeout = opts.deferHeavy ? (opts.timeout || 1800) : (opts.timeout || 900)
    scheduleVisualApply(runHeavyCoverWork, heavyDelay, heavyTimeout)
  })().catch(function(e){ console.warn('[深度缓存] 异步加载失败', e) })
}

// ============================================================
//  插件端节奏分析已移除
//    频谱、节拍和波形只来自 EchoMusic 宿主推送。
// ============================================================
// 生成节拍图缓存键，用于把宿主推送的节拍数据和当前歌曲关联。
function beatMapSongKey(song) {
  // 无歌曲时没有可缓存的 key。
  if (!song) return '';
  // 本地歌曲优先使用 localKey，避免同名歌曲冲突。
  if (song.type === 'local' && song.localKey) return 'local:' + song.localKey;
  // QQ 音乐歌曲优先使用 mid/songmid/id，最后才退回歌名和歌手。
  if (songProviderKey(song) === 'qq') return 'qq:' + (song.mid || song.songmid || song.id || (song.name + '|' + song.artist));
  // 其他来源有稳定 id 时使用通用 song 前缀。
  if (song.id != null && song.id !== '') return 'song:' + song.id;
  return '';
}

// 隐藏节拍状态提示胶囊。
function hideBeatChip() {
  document.getElementById('beat-chip').classList.remove('show');
}

// 每帧调用 — 按 beatMap 触发预演鼓点
// 根据当前播放时间同步普通节拍图游标，并可选择保留当前视觉状态。
function syncBeatMapPlaybackCursor(t, preserveVisualState) {
  // DJ 模式使用独立节拍图和游标。
  if (djMode.active) {
    syncDjBeatMapCursor(t, preserveVisualState);
    return;
  }
  // 播放时间归一化，非法值按 0 处理。
  t = isFinite(t) ? t : 0;
  // 从头扫描到当前时间对应的下一个脉冲位置。
  beatMapNextIdx = 0;
  // 优先使用脉冲节拍，兼容旧数据中的 kicks。
  var pulseEvents = currentBeatMap && (currentBeatMap.pulseBeats || currentBeatMap.kicks);
  if (pulseEvents) {
    while (beatMapNextIdx < pulseEvents.length && beatEventTime(pulseEvents[beatMapNextIdx]) < t) beatMapNextIdx++;
  }
  // 保留视觉状态时只对齐相机游标，否则把相机同步到当前时间。
  if (preserveVisualState) alignBeatCameraCursorToTime(t);
  else syncBeatCameraToTime(t);
}

// 根据当前播放时间同步 DJ 模式节拍图游标。
function syncDjBeatMapCursor(t, preserveVisualState) {
  // 播放时间归一化。
  t = isFinite(t) ? t : 0;
  // DJ 相机节拍游标。
  djBeatMapNextIdx = 0;
  // DJ 粒子脉冲游标。
  djBeatPulseNextIdx = 0;
  if (currentDjBeatMap) {
    // 相机节拍兼容 cameraBeats、beats、kicks 三种字段。
    var beatEvents = currentDjBeatMap.cameraBeats || currentDjBeatMap.beats || currentDjBeatMap.kicks || [];
    // 相机节拍略微提前对齐，避免视觉动作落后听感。
    var camSyncTime = Math.max(0, t - 0.025);
    while (djBeatMapNextIdx < beatEvents.length && beatEventTime(beatEvents[djBeatMapNextIdx]) < camSyncTime) djBeatMapNextIdx++;
    // 脉冲节拍兼容 pulseBeats 和 kicks。
    var pulseEvents = currentDjBeatMap.pulseBeats || currentDjBeatMap.kicks || [];
    // 脉冲也略微提前对齐，让切换后立即落在正确节拍窗口。
    var pulseSyncTime = Math.max(0, t - 0.035);
    while (djBeatPulseNextIdx < pulseEvents.length && beatEventTime(pulseEvents[djBeatPulseNextIdx]) < pulseSyncTime) djBeatPulseNextIdx++;
  }
  // 不保留视觉状态时重置相机节拍同步状态。
  if (!preserveVisualState) resetBeatCameraSync(t);
}

// 播放中按 DJ 节拍图触发相机动作和粒子脉冲。
function tickDjBeatMap() {
  // 仅在 DJ 模式、有节拍图且音频播放中工作。
  if (!djMode.active || !currentDjBeatMap || !audio || audio.paused) return;
  // 当前播放时间。
  var t = audio.currentTime || 0;
  // 部分节拍图只覆盖前段，超过覆盖区和预读窗口后停止调度。
  if (currentDjBeatMap.partialUntilSec && t > currentDjBeatMap.partialUntilSec + beatCam.lookahead) return;
  // 相机节拍事件列表。
  var beatEvents = currentDjBeatMap.cameraBeats || currentDjBeatMap.beats || currentDjBeatMap.kicks || [];
  // 粒子脉冲事件列表。
  var pulseEvents = currentDjBeatMap.pulseBeats || currentDjBeatMap.kicks || [];
  // 在预读窗口内提前调度相机动作。
  while (djBeatMapNextIdx < beatEvents.length) {
    // 当前待调度相机节拍。
    var beat = beatEvents[djBeatMapNextIdx];
    // 当前节拍时间。
    var beatTime = beatEventTime(beat);
    if (beatTime > t + beatCam.lookahead) break;
    scheduleBeatCamera(beat, 'djmap');
    djBeatMapNextIdx++;
  }
  // 到达当前时间的脉冲立即触发。
  while (djBeatPulseNextIdx < pulseEvents.length && beatEventTime(pulseEvents[djBeatPulseNextIdx]) <= t) {
    triggerScheduledBeat(pulseEvents[djBeatPulseNextIdx]);
    djBeatPulseNextIdx++;
  }
}

// 播放中按普通节拍图触发相机动作和粒子脉冲。
function tickBeatMap() {
  // DJ 模式由 tickDjBeatMap 接管。
  if (djMode.active) return;
  // 无节拍图或未播放时不调度。
  if (!currentBeatMap || !audio || audio.paused) return;
  // 当前播放时间。
  var t = audio.currentTime;
  // 相机节拍事件列表。
  var beatEvents = currentBeatMap.cameraBeats || currentBeatMap.beats || currentBeatMap.kicks || [];
  // 粒子脉冲事件列表。
  var pulseEvents = currentBeatMap.pulseBeats || currentBeatMap.kicks || [];
  // 宿主节拍网格可信且数量足够时，优先按网格驱动。
  var gridTimingLocked = currentBeatMap.tempoSource === 'host' && beatEvents.length >= 4;
  // 实时节拍锁定的新鲜窗口，超过窗口说明实时节拍暂时不可靠。
  var liveFreshWindow = Math.max(0.50, rtBeat.tempoGap ? rtBeat.tempoGap * 1.18 : 0.50);
  // 实时节拍是否仍处于锁定状态。
  var realtimeHasLock = rtBeat.lastHitAt > 0 && (t - rtBeat.lastHitAt) < liveFreshWindow;
  // 在预读窗口内调度相机节拍。
  while (beatCam.nextIdx < beatEvents.length) {
    // 当前待调度相机节拍。
    var beat = beatEvents[beatCam.nextIdx];
    // 支持数字节拍和对象节拍两种格式。
    var beatTime = typeof beat === 'number' ? beat : beat.time;
    if (beatTime > t + beatCam.lookahead) break;
    // 若实时节拍仍锁定且宿主网格不可靠，则避免重复触发相机动作。
    if (gridTimingLocked || !realtimeHasLock) scheduleBeatCamera(beat, 'map');
    beatCam.nextIdx++;
  }
  // 到达当前时间的脉冲节拍触发粒子冲击。
  while (beatMapNextIdx < pulseEvents.length && beatEventTime(pulseEvents[beatMapNextIdx]) <= t) {
    // 触发预演冲击
    if (gridTimingLocked || !realtimeHasLock) triggerScheduledBeat(pulseEvents[beatMapNextIdx]);
    beatMapNextIdx++;
  }
}

// 把节拍事件转换为下一帧 shader 可消费的脉冲强度。
function triggerScheduledBeat(beat) {
  // 节拍基础强度，数字节拍直接使用默认或数字值，对象节拍读取 strength。
  var strength = typeof beat === 'number' ? 0.42 : Math.max(0, Math.min(1, beat && beat.strength != null ? beat.strength : 0.42));
  // impact 表示视觉冲击强度，缺省回退到 strength。
  var impact = typeof beat === 'number' ? strength : Math.max(0, Math.min(1, beat && beat.impact != null ? beat.impact : strength));
  // 过弱事件不触发，减少微小误检导致的画面抖动。
  if (impact < 0.18 && strength < 0.52) return;
  // 动态缩放很低时进一步过滤弱事件，避免安静歌曲视觉过度。
  if ((cinemaTrackProfile.scale || 1) < 0.52 && impact < 0.46 && strength < 0.74) return;
  // body 表示低频身体感，用于增加粒子脉冲厚度。
  var body = typeof beat === 'number' ? 0 : Math.max(0, Math.min(1, beat && beat.body != null ? beat.body : 0));
  // combo 描述下拍、drop 等组合节拍。
  var combo = typeof beat === 'number' ? null : beat && beat.combo;
  // 特殊组合节拍给少量额外抬升。
  var comboLift = combo === 'downbeat' ? 0.08 : (combo === 'drop' ? 0.04 : 0);
  // 根据当前电影化曲线缩放脉冲强度。
  var dynScale = cameraDynamicsScale(0.88 + impact * 0.16);
  // DJ 节拍采用单独的强度上限和权重。
  var djPulse = beat && beat.dj;
  // 综合多个节拍维度得到最终脉冲候选值。
  var pulse = (0.14 + strength * 0.46 + impact * 0.18 + body * 0.08 + comboLift) * dynScale;
  if (djPulse) pulse = (0.12 + strength * 0.50 + impact * 0.28 + comboLift * 0.70) * clampRange(dynScale, 0.78, 1.18);
  // 控制普通和 DJ 脉冲上限。
  pulse = Math.min(djPulse ? 0.92 : 0.78, pulse);
  // 同一帧内多个事件取最大脉冲。
  scheduledBeatPulse = Math.max(scheduledBeatPulse, pulse);
  // 标记下一帧需要消费节拍脉冲。
  scheduledBeatFlag = true;
}
// 下一帧待消费的节拍脉冲强度。
var scheduledBeatPulse = 0;
// 下一帧是否存在待消费节拍脉冲。
var scheduledBeatFlag = false;

// 显示 AI 深度处理状态提示。
function showAIDepthChip(text) {
  document.getElementById('ai-depth-text').textContent = text || 'AI 深度估计…';
  document.getElementById('ai-depth-chip').classList.add('show');
}
// 隐藏 AI 深度处理状态提示。
function hideAIDepthChip() {
  document.getElementById('ai-depth-chip').classList.remove('show');
}

// 从远程 URL 加载封面，裁剪成方形 canvas 后交给封面应用链路。
function loadCoverFromUrl(directUrl, opts) {
  // URL 封面加载会先走代理以规避跨域 canvas 污染；失败后再尝试原始地址作为降级。
  opts = opts || {};
  if (!directUrl || typeof directUrl !== 'string' || !/^https?:\/\//i.test(directUrl)) {
    // 空封面也要递增 token，这样已经在途的旧图片或旧 AI 深度结果不会回写到空状态。
    if (!coverApplyStillCurrent(opts)) return;
    // 清除当前封面来源记录。
    currentCoverSource = null;
    // 递增封面处理 token，让旧异步任务失效。
    coverProcessToken++;
    // 关闭封面和深度状态。
    uniforms.uHasCover.value = 0; setCoverDepthState(0, 0, 1);
    // 浮空粒子回到空闲配色。
    resetFloatColorsToIdle();
    // 隐藏背景封面。
    document.getElementById('album-bg').classList.remove('visible');
    // 清空底部缩略图。
    document.getElementById('thumb-cover').removeAttribute('src');
    // 清空控制条封面。
    setControlCoverSrc('');
    return;
  }
  // 先用原始地址更新背景图，背景不需要读像素，因此不受 canvas 跨域限制。
  document.getElementById('album-bg').style.backgroundImage = "url(" + directUrl + ")";
  document.getElementById('album-bg').classList.add('visible');
  // 生成代理 URL，供后续 canvas 读像素和深度处理使用。
  var proxiedUrl = coverProxySrc(directUrl);
  if (!proxiedUrl) {
    // 没有可用代理时关闭封面纹理，只保留背景图降级。
    uniforms.uHasCover.value = 0; setCoverDepthState(0, 0, 1);
    resetFloatColorsToIdle();
    setControlCoverSrc('');
    return;
  }
  // 通过代理加载可跨域读取像素的图片。
  var img = new Image(); img.crossOrigin = 'anonymous'; img.decoding = 'async';
  img.onload = function() {
    // 图片加载完成后再裁剪为正方形 canvas，供封面纹理和深度流水线共用。
    if (!coverApplyStillCurrent(opts)) return;
    // 根据当前封面分辨率偏好决定纹理尺寸。
    var size = coverTextureSizeForResolution(fx.coverResolution);
    // 创建方形封面 canvas。
    var cv = document.createElement('canvas'); cv.width = cv.height = size;
    // 方形封面绘制上下文。
    var cx = cv.getContext('2d');
    // 原图尺寸和中心裁剪边长。
    var iw = img.naturalWidth, ih = img.naturalHeight, s = Math.min(iw, ih);
    cx.drawImage(img, (iw-s)/2, (ih-s)/2, s, s, 0, 0, size, size);
    // 进入统一封面应用链路，并保留原始 URL 作为缓存 key。
    applyCoverCanvas(cv, proxiedUrl || directUrl, Object.assign({}, opts, { coverKey: directUrl || proxiedUrl || '', coverSourceKind: 'url', coverSource: directUrl }));
  };
  img.onerror = function() {
    // 代理加载失败时回退到原始地址加载。
    var img2 = new Image(); img2.crossOrigin = 'anonymous'; img2.decoding = 'async';
    img2.onload = function() {
      // 回退图片加载完成后仍要防串。
      if (!coverApplyStillCurrent(opts)) return;
      // 回退路径使用同一封面尺寸。
      var size = coverTextureSizeForResolution(fx.coverResolution);
      // 创建方形封面 canvas。
      var cv = document.createElement('canvas'); cv.width = cv.height = size;
      cv.getContext('2d').drawImage(img2, 0, 0, size, size);
      // 回退路径进入统一封面应用链路。
      applyCoverCanvas(cv, directUrl, Object.assign({}, opts, { coverKey: directUrl || '', coverSourceKind: 'url', coverSource: directUrl }));
    };
    img2.onerror = function() {
      // 两次加载都失败时，只清空可读封面纹理和相关 UI。
      if (!coverApplyStillCurrent(opts)) return;
      currentCoverSource = null;
      uniforms.uHasCover.value = 0; setCoverDepthState(0, 0, 1);
      resetFloatColorsToIdle();
      setControlCoverSrc('');
    };
    // 启动原始地址回退加载。
    img2.src = directUrl;
  };
  // 启动代理地址加载。
  img.src = proxiedUrl;
}

// 设置页面背景层的封面图显示状态。
function setAlbumBackground(src) {
  // 背景节点可能在精简布局中不存在。
  var bg = document.getElementById('album-bg');
  if (!bg) return;
  if (!src) {
    // 无地址时隐藏背景并清空背景图。
    bg.classList.remove('visible');
    bg.style.backgroundImage = '';
    return;
  }
  // 有地址时写入背景图并显示。
  bg.style.backgroundImage = "url(" + src + ")";
  bg.classList.add('visible');
}

// 将任意图片绘制为指定尺寸的方形封面 canvas。
function makeSquareCoverCanvas(img, size, crop) {
  // 默认输出 512 像素方图。
  size = size || 512;
  // 输出封面 canvas。
  var cv = document.createElement('canvas');
  cv.width = cv.height = size;
  // 输出 canvas 绘制上下文。
  var cx = cv.getContext('2d');
  cx.clearRect(0, 0, size, size);
  // 图片原始宽度。
  var iw = img.naturalWidth || img.width;
  // 图片原始高度。
  var ih = img.naturalHeight || img.height;
  if (crop) {
    // 调用方已指定裁剪区域时直接按指定区域裁切。
    cx.drawImage(img, crop.sx, crop.sy, crop.sSize, crop.sSize, 0, 0, size, size);
  } else {
    // 未指定裁剪时取中心最大正方形区域。
    var s = Math.min(iw, ih);
    cx.drawImage(img, (iw - s) / 2, (ih - s) / 2, s, s, 0, 0, size, size);
  }
  return cv;
}

// 应用宿主直接传入的 dataURL 封面。
function applyCoverDataUrl(dataUrl, opts) {
  // 宿主可能直接推送内联封面，dataUrl 路径不需要代理，但仍必须走同一套 token 校验和 canvas 处理。
  opts = opts || {};
  if (!dataUrl) return;
  // dataURL 图片对象。
  var img = new Image();
  img.decoding = 'async';
  img.onload = function() {
    // 解码完成后防串。
    if (!coverApplyStillCurrent(opts)) return;
    // 按当前封面分辨率生成方形 canvas。
    var cv = makeSquareCoverCanvas(img, coverTextureSizeForResolution(fx.coverResolution));
    // dataURL 可直接用于背景层。
    setAlbumBackground(dataUrl);
    // 进入统一封面应用链路，并记录来源为 data。
    applyCoverCanvas(cv, dataUrl, Object.assign({}, opts, { coverSourceKind: 'data', coverSource: dataUrl }));
  };
  // 启动 dataURL 解码。
  img.src = dataUrl;
}



// ===== js/05-playlist-shelf.js =====

// ============================================================
//  3D 歌单架 — 双模式 (off / side / stage)
//   - side:   现版本精修, 右侧 5 张卡微角度堆叠
//   - stage:  弧形排列, 居中, 有倒影, 当前卡片"呼吸+光环"
//             卡片间粒子穿梭, 切歌时飞出动画
// ============================================================
// 歌单架是否被用户固定展开。
var shelfPinnedOpen = false;
// 歌单架管理器实例，负责创建和更新 3D 卡片。
var shelfManager = null;
// 最近一次打开歌单架的动画起始时间。
var shelfOpenAnimAt = -10;
// 侧边歌单架悬停提示状态，记录目标显隐、当前位置和热区停留时间。
var shelfHoverCue = { target: 0, value: 0, x: 0, y: 0, lastAt: 0, enteredAt: 0, zoneActive: false };
var shelfVisibility = 0;  // 0..1, 侧栏自动隐藏的整体透明度系数
// 判断应用是否已经完成启动揭示，兼容旧入口和迁移后的桥接入口。
function isShelfAppRevealed() {
  // 迁移后的桥接入口没有旧版启动揭示流程，缺失时按已揭示处理。
  return typeof appRevealed === 'undefined' ? true : !!appRevealed;
}
// 判断当前视口是否更适合竖屏歌单架布局。
function isPortraitShelfViewport() {
  return innerHeight > innerWidth * 1.08;
}
// 计算歌单架在当前视口、预设和用户设置下的布局参数。
function shelfLayoutProfile() {
  // 歌单架布局按横竖屏、窄屏和骷髅预设分别收敛，避免卡片压住主视觉或歌词。
  // 是否竖屏。
  var portrait = isPortraitShelfViewport();
  // 横屏但宽度较小的窄屏布局标记。
  var narrow = !portrait && innerWidth < 980;
  // 骷髅预设需要更保守的右侧安全区域。
  var skullShelf = shouldUseSkullSafeShelfCamera();
  // 二级详情面板的基础缩放。
  var detailScale = portrait ? clampRange(innerWidth / 820, 0.70, 0.86) : (narrow ? 0.92 : 1.04);
  // 用户在设置面板中调整的歌单架偏移、角度和大小。
  var shelfCtl = shelfSettings();
  return {
    // 是否竖屏，供调用方复用。
    portrait: portrait,
    // 是否窄屏，供调用方复用。
    narrow: narrow,
    // 侧边模式卡片基准 X 坐标。
    sideX: (skullShelf ? (portrait ? 0.22 : (narrow ? 0.46 : 0.76)) : (portrait ? 1.56 : (narrow ? 2.48 : 3.18))) + shelfCtl.x,
    // 侧边模式卡片基准 Y 坐标。
    sideY: (skullShelf ? (portrait ? -0.22 : (narrow ? -0.30 : -0.34)) : 0) + shelfCtl.y,
    // 侧边模式相邻卡片 X 方向错位。
    sideXStep: skullShelf ? (portrait ? 0.018 : 0.034) : (portrait ? 0.018 : 0.040),
    // 侧边模式相邻卡片 Y 方向错位。
    sideYStep: skullShelf ? (portrait ? 0.46 : 0.62) : (portrait ? 0.52 : 0.68),
    // 侧边模式基准 Z 深度。
    sideZ: (skullShelf ? (portrait ? 0.86 : 0.92) : (portrait ? 0.78 : 0.86)) + shelfCtl.z,
    // 侧边模式相邻卡片 Z 方向错位。
    sideZStep: skullShelf ? (portrait ? 0.108 : 0.158) : (portrait ? 0.118 : 0.170),
    // 侧边模式入场动画的 X 起点偏移。
    sideEntryX: skullShelf ? (portrait ? 0.30 : 0.50) : (portrait ? 0.38 : 0.82),
    // 侧边详情打开时主卡片额外位移。
    sideDetailShift: skullShelf ? (portrait ? 0.00 : 0.00) : (portrait ? 0.38 : 0.82),
    // 侧边模式卡片缩放。
    sideScale: (skullShelf ? (portrait ? 0.84 : (narrow ? 1.04 : 1.22)) : (portrait ? 0.70 : (narrow ? 0.86 : 1))) * shelfCtl.size,
    // 侧边模式卡片 Y 轴旋转。
    sideRotY: (skullShelf ? (portrait ? -0.085 : -0.190) : (portrait ? 0.12 : 0.28)) + shelfCtl.angle,
    // 侧边模式卡片 X 轴俯仰。
    sideRotX: skullShelf ? (portrait ? 0.018 : 0.030) : (portrait ? 0.022 : 0.042),
    // 舞台模式基准 X 坐标。
    stageX: shelfCtl.x,
    // 舞台模式卡片横向间距。
    stageXStep: portrait ? 0.92 : (narrow ? 1.22 : 1.55),
    // 舞台模式基准 Y 坐标。
    stageY: (portrait ? -2.46 : -2.20) + shelfCtl.y,
    // 舞台模式基准 Z 深度。
    stageZ: (portrait ? 0.84 : 1.0) + shelfCtl.z,
    // 舞台模式卡片缩放。
    stageScale: (portrait ? 0.72 : (narrow ? 0.86 : 1)) * shelfCtl.size,
    // 二级内容面板布局参数。
    detail: {
      // 详情面板基准 X 坐标。
      x: (skullShelf ? (portrait ? 0.16 : (narrow ? 0.40 : 0.64)) : (portrait ? 0.38 : (narrow ? 0.96 : 1.28))) + shelfCtl.x * 0.62,
      // 详情面板基准 Y 坐标。
      y: (skullShelf ? (portrait ? -0.40 : -0.68) : (portrait ? 0.10 : 0.18)) + shelfCtl.y * 0.55,
      // 详情面板基准 Z 深度。
      z: (skullShelf ? (portrait ? 1.10 : 1.22) : (portrait ? 1.28 : 1.36)) + shelfCtl.z * 0.45,
      // 详情面板 X 轴旋转。
      rx: skullShelf ? (portrait ? 0.006 : 0.014) : (portrait ? -0.004 : -0.008),
      // 详情面板 Y 轴旋转。
      ry: (skullShelf ? (portrait ? -0.070 : -0.165) : (portrait ? 0.00 : 0.020)) + shelfCtl.angle * 0.55,
      // 详情面板整体缩放。
      scale: (skullShelf ? detailScale * (portrait ? 0.88 : 1.02) : detailScale) * shelfCtl.size,
      // 详情面板内行间距。
      rowStep: skullShelf ? (portrait ? 0.37 : 0.43) : (portrait ? 0.36 : 0.42),
      // 详情面板内行缩放。
      rowScale: skullShelf ? (portrait ? 0.90 : 1.02) : (portrait ? 0.88 : (narrow ? 0.96 : 1.00))
    }
  };
}
// 计算右侧悬停热区宽度。
function shelfHotZoneWidth() {
  // 竖屏热区比例更宽，方便触摸和窄屏操作。
  var ratio = isPortraitShelfViewport() ? 0.26 : 0.18;
  return Math.min(isPortraitShelfViewport() ? 280 : 360, Math.max(148, innerWidth * ratio));
}
// 计算预览可用热区宽度，用于判断侧栏预览是否应继续保持。
function shelfPreviewUseZoneWidth() {
  return Math.min(820, Math.max(shelfHotZoneWidth(), innerWidth * 0.56));
}
// 计算滚轮控制歌单架的右侧热区宽度。
function shelfWheelZoneWidth() {
  // 竖屏滚轮热区略窄，避免影响主体滚动区域。
  var portrait = isPortraitShelfViewport();
  // 按视口比例得到候选宽度。
  var ratioWidth = innerWidth * (portrait ? 0.24 : 0.18);
  return Math.min(portrait ? 280 : 360, Math.max(shelfHotZoneWidth(), ratioWidth));
}
// 判断一次点击是否落在侧边歌单架交互区域。
function isShelfClickZone(e) {
  // 固定展开时扩大点击区域，否则使用悬停热区。
  var edge = shelfPinnedOpen ? Math.min(390, Math.max(210, innerWidth * 0.22)) : shelfHotZoneWidth();
  return e.clientX > innerWidth - edge && e.clientY > 130 && e.clientY < innerHeight - 150;
}
// 判断指针是否处在允许继续使用侧边预览的区域。
function isShelfPreviewUseZone(e) {
  // 预览区比热区宽，允许用户从边缘移向展开卡片。
  var edge = shelfPreviewUseZoneWidth();
  return e.clientX > innerWidth - edge && e.clientY > 96 && e.clientY < innerHeight - 96;
}
// 判断滚轮事件是否应交给歌单架处理。
function isShelfWheelZone(e) {
  // 滚轮区使用独立宽度，减少误拦截主页面滚轮。
  var edge = shelfWheelZoneWidth();
  return e.clientX > innerWidth - edge && e.clientY > 116 && e.clientY < innerHeight - 116;
}
// 判断侧边歌单架在未固定展开时是否仍可显示。
function canUseSideShelfWithoutPinnedOpen() {
  return !!shelfAlwaysVisible();
}
// 判断歌单架预览当前是否可见或正在过渡中。
function shelfPreviewIsVisible() {
  return shelfHoverCue.zoneActive || shelfHoverCue.target > 0 || shelfHoverCue.value > 0.10 || shelfVisibility > 0.12;
}
// 判断自动隐藏状态下的歌单架是否可以响应输入。
function shelfAutoHiddenInputReady() {
  // 固定展开或设置为常显时始终可交互。
  if (shelfPinnedOpen || shelfAlwaysVisible()) return true;
  // 已打开二级内容时保持可交互。
  if (shelfManager && shelfManager.hasOpenContent && shelfManager.hasOpenContent()) return true;
  return !!(shelfHoverCue.zoneActive || shelfHoverCue.value > 0.18 || shelfVisibility > 0.16);
}
// 判断当前位置是否可以显示悬停提示；当前版本关闭该提示。
function canShowShelfHoverCueAt(e) {
  return false;
}
// 获取侧边悬停提示热区矩形。
function shelfCueRect() {
  // 热区宽度。
  var w = shelfHotZoneWidth();
  // 热区顶部，避开顶部标题和控制区域。
  var top = Math.max(136, innerHeight * 0.22);
  // 热区高度，避开底部播放控制条。
  var h = Math.min(390, innerHeight - top - 142);
  return { left: innerWidth - w, top: top, width: w, height: h, right: innerWidth, bottom: top + h };
}
// 获取悬停提示热区的视觉中心点。
function shelfCueCenter() {
  // 当前热区矩形。
  var r = shelfCueRect();
  return { x: r.left + r.width * 0.58, y: r.top + r.height * 0.50 };
}
// 根据指针位置更新歌单架悬停提示目标状态。
function updateShelfHoverCueFromPointer(e) {
  if (!e) {
    // 指针离开时重置悬停提示状态。
    shelfHoverCue.target = 0;
    shelfHoverCue.zoneActive = false;
    shelfHoverCue.enteredAt = 0;
    return;
  }
  // 当前指针是否激活提示。
  var active = false;
  // 当前指针是否位于提示热区。
  var inZone = canShowShelfHoverCueAt(e);
  if (inZone && !shelfHoverCue.zoneActive) {
    // 刚进入热区时记录进入时间，用于延迟显示。
    shelfHoverCue.zoneActive = true;
    shelfHoverCue.enteredAt = performance.now();
  } else if (!inZone) {
    // 离开热区时清除停留时间。
    shelfHoverCue.zoneActive = false;
    shelfHoverCue.enteredAt = 0;
  }
  active = inZone;
  // 更新目标显隐和最后指针位置。
  shelfHoverCue.target = active ? 1 : 0;
  shelfHoverCue.x = e.clientX;
  shelfHoverCue.y = e.clientY;
  shelfHoverCue.lastAt = performance.now();
}
// 每帧推进歌单架悬停提示显隐插值。
function tickShelfHoverCue(dt) {
  if (shelfHoverCue.zoneActive) {
    // 用最近一次指针位置重新验证热区，避免窗口尺寸变化后状态滞留。
    var heldPointer = { clientX: shelfHoverCue.x, clientY: shelfHoverCue.y };
    if (canShowShelfHoverCueAt(heldPointer)) {
      // 停留超过阈值后才显示提示，降低误触发。
      if (performance.now() - shelfHoverCue.enteredAt > 260) shelfHoverCue.target = 1;
    } else {
      // 热区失效时立即收起提示。
      shelfHoverCue.zoneActive = false;
      shelfHoverCue.enteredAt = 0;
      shelfHoverCue.target = 0;
    }
  }
  // 指针长时间未更新时收起提示。
  if (!shelfHoverCue.zoneActive && performance.now() - shelfHoverCue.lastAt > 650) shelfHoverCue.target = 0;
  // 当前目标值。
  var target = shelfHoverCue.target;
  // 显示和隐藏使用略不同的速度。
  var rate = target > shelfHoverCue.value ? 0.12 : 0.10;
  // 根据帧间隔推进 value。
  shelfHoverCue.value += (target - shelfHoverCue.value) * Math.min(1, rate * Math.max(1, dt * 60));
  // 接近 0 时吸附为 0，避免残留透明度。
  if (shelfHoverCue.value < 0.006 && !target) shelfHoverCue.value = 0;
  return shelfHoverCue.value;
}
// 设置歌单架是否固定展开。
function setShelfPinnedOpen(open, immediate) {
  // 归一化目标展开状态。
  var nextOpen = !!open;
  // 展开歌单架时暂时压制底部控制条，避免互相遮挡。
  if (nextOpen && typeof suppressBottomControlsForShelf === 'function') suppressBottomControlsForShelf(980);
  if (nextOpen && !shelfPinnedOpen) {
    // 使用 shader 时间作为动画时间基准。
    var nowT = uniforms && uniforms.uTime ? uniforms.uTime.value : performance.now() / 1000;
    // 如果预览已经可见，则打开动画从更靠后的进度开始，避免重复入场。
    var previewVisible = shelfHoverCue.value > 0.28 || shelfVisibility > 0.20;
    shelfOpenAnimAt = previewVisible ? nowT - 0.62 : nowT;
    // 固定展开后收起悬停提示。
    shelfHoverCue.target = 0;
    shelfHoverCue.zoneActive = false;
    shelfHoverCue.enteredAt = 0;
  }
  // 写入固定展开状态。
  shelfPinnedOpen = nextOpen;
  // 主提示在歌单架固定或打开内容时隐藏。
  var hint = document.getElementById('hint');
  if (hint) hint.classList.toggle('shelf-hidden', shelfPinnedOpen || !!(shelfManager && shelfManager.hasOpenContent && shelfManager.hasOpenContent()));
  // 已打开二级内容时不切换焦点区，避免打断内容交互。
  if (shelfManager && shelfManager.hasOpenContent && shelfManager.hasOpenContent()) return;
  // 同步相机焦点区。
  if (typeof setFocusZone === 'function') setFocusZone(shelfPinnedOpen ? 'shelf-side' : null, immediate);
}
// 指针离开或模式重置时清理侧边歌单架预览状态。
function clearShelfPreviewOnPointerExit() {
  // 只处理 side 模式。
  if (!shelfManager || !shelfManager.getMode || shelfManager.getMode() !== 'side') return;
  // 是否有二级内容打开。
  var hasContent = shelfManager.hasOpenContent && shelfManager.hasOpenContent();
  // 清空悬停提示和预览透明度。
  updateShelfHoverCueFromPointer(null);
  shelfHoverCue.target = 0;
  shelfHoverCue.value = 0;
  shelfHoverCue.zoneActive = false;
  shelfHoverCue.enteredAt = 0;
  // 隐藏侧边悬停标签。
  if (typeof setShelfHoverTabVisible === 'function') setShelfHoverTabVisible(false);
  // 清除当前选中卡片。
  if (shelfManager && shelfManager.clearSelected) shelfManager.clearSelected();
  // 如果有内容面板，安全关闭。
  if (hasContent && shelfManager.closeContent) safeShelfCloseContent('shelf-mode-reset');
  // 固定展开时同步关闭固定状态。
  if (shelfPinnedOpen) setShelfPinnedOpen(false, true);
  // 常驻模式下不清零可见度，避免鼠标离开时歌单架闪烁。
  if (!shelfAlwaysVisible()) {
    shelfVisibility = 0;
  }
  // 清空相机焦点区。
  if (typeof setFocusZone === 'function') setFocusZone(null, true);
}
// 切歌时压制侧边预览，避免新歌开始时旧卡片仍浮出。
function suppressShelfPreviewForPlaybackSwitch() {
  // 只处理 side 模式。
  if (!shelfManager || !shelfManager.getMode || shelfManager.getMode() !== 'side') return;
  // 固定展开或已有内容时不强制收起。
  if (shelfPinnedOpen || (shelfManager.hasOpenContent && shelfManager.hasOpenContent())) return;
  // 清空悬停提示和选择。
  updateShelfHoverCueFromPointer(null);
  shelfHoverCue.target = 0;
  shelfHoverCue.value = 0;
  shelfHoverCue.zoneActive = false;
  shelfHoverCue.enteredAt = 0;
  shelfVisibility = 0;
  if (typeof setShelfHoverTabVisible === 'function') setShelfHoverTabVisible(false);
  if (shelfManager && shelfManager.clearSelected) shelfManager.clearSelected();
  // 切歌后焦点回到主视觉。
  if (typeof setFocusZone === 'function') setFocusZone(null, true);
}
function makeShelfManager() {
  // 歌单架管理器只暴露交互和刷新接口；内部维护 Three.js 组、卡片窗口、二级列表和舞台装饰。
  // 歌单架 Three.js 根组。
  var group = null;
  // 当前实际渲染出来的卡片窗口。
  var cards = [];          // [{canvas, ctx, texture, mesh, item, index, slot}]
  // 当前歌单架可展示的完整条目列表。
  var allItems = [];
  // 只渲染中心附近的一小段卡片窗口，长队列不会一次性创建所有 canvas/texture/mesh。
  // 当前窗口在 allItems 中的起始索引。
  var renderedStart = -1;
  // 中心卡片前后各保留的可见半径。
  var SHELF_VISIBLE_RADIUS = 5;
  // 单次最多渲染的卡片数。
  var SHELF_MAX_RENDER = SHELF_VISIBLE_RADIUS * 2 + 1;
  // 二级面板切换动画起始时间。
  var paneSwitchAt = -10;
  // 二级面板切换方向。
  var paneSwitchDir = 1;
  // 歌单架显示模式，默认侧边模式。
  var mode = 'side';
  // 上一次条目签名，用于判断是否需要重建卡片窗口。
  var lastSig = '';
  // 上一次整体更新的时间戳。
  var lastUpdate = 0;
  // 上一次卡片重绘时间。
  var lastCardRedrawAt = -10;
  // 上一次用于卡片节奏脉冲的桶值。
  var lastCardPulseBucket = -1;
  // 分帧构建卡片的队列状态。
  var cardBuildQueue = null;
  // 当前鼠标或键盘选中的卡片索引。
  var selectedIdx = -1;

  // v7.2 PSP 风格状态
  var centerIdx = 0;          // 当前居中卡片 index (在 items 数组中的位置)
  var centerTarget = 0;       // 目标 centerIdx (插值)
  var centerSmooth = 0;       // 当前实际 centerIdx 平滑值
  var openCardIdx = -1;       // 已打开内容框的卡片 (-1 表示无)
  var contentList = null;     // 二级 PSP 滚动列表 manager
  // 舞台模式中连接卡片的粒子装饰。
  var connectorParticles = null;
  // 舞台模式地面倒影网格。
  var floorMirror = null;

  // 根据播放队列生成歌单架条目列表。
  function currentItems() {
    if (playQueue.length) {
      // 播放队列中的每首歌映射为一个 queue 类型卡片。
      return playQueue.map(function(song, idx){
        return { type:'queue', title: song.name, sub: song.artist || '未知歌手',
          cover: songCoverSrc(song, 360), tag: idx === currentIdx ? '正在播放' : ('#' + (idx+1)), queueIndex: idx };
      });
    }
    // 无播放队列时歌单架为空。
    return [];
  }

  // 在 canvas 上构造圆角矩形路径。
  function makeRoundRect(ctx, x, y, w, h, r) {
    ctx.beginPath();
    ctx.moveTo(x+r,y); ctx.arcTo(x+w,y,x+w,y+h,r); ctx.arcTo(x+w,y+h,x,y+h,r);
    ctx.arcTo(x,y+h,x,y,r); ctx.arcTo(x,y,x+w,y,r); ctx.closePath();
  }
  // 按最大宽度和最大行数在 canvas 上绘制自动换行文本。
  function wrapText(ctx, text, x, y, maxWidth, lineHeight, maxLines) {
    // 逐字拆分，适配中文没有空格分词的标题。
    var chars = String(text || '').split('');
    // 当前行文本和最终行数组。
    var line = '', lines = [];
    for (var i = 0; i < chars.length; i++) {
      // 尝试把当前字符追加到当前行。
      var test = line + chars[i];
      if (ctx.measureText(test).width > maxWidth && line) {
        // 超出宽度时换行。
        lines.push(line); line = chars[i];
        // 预留最后一行后停止继续收集。
        if (lines.length >= maxLines - 1) break;
      } else line = test;
    }
    // 收尾时把最后一行加入列表。
    if (line && lines.length < maxLines) lines.push(line);
    // 逐行绘制文本。
    for (var j = 0; j < lines.length; j++) ctx.fillText(lines[j], x, y + j * lineHeight);
  }
  // 生成卡片绘制签名，用于判断 canvas 内容是否需要重绘。
  function cardDrawSignature(card, item) {
    item = item || {};
    // 封面缓存记录。
    var rec = item.cover ? playlistCoverCache[item.cover] : null;
    // 封面加载状态参与签名，加载完成后可触发重绘。
    var coverState = item.cover ? (rec && rec.loaded ? 'ready' : (rec && rec.failed ? 'fail' : 'wait')) : 'none';
    // 中心卡片根据节奏脉冲分桶，避免每帧都重绘 canvas。
    var pulseBucket = card && card.isCenter ? Math.round((bass + beatPulse * 0.85) * 6) : 0;
    return [
      item.type || '', item.title || '', item.sub || '', item.tag || '',
      item.playlistId || '', item.queueIndex == null ? '' : item.queueIndex,
      item.cover || '', coverState, card && card.isCenter ? 1 : 0, card && card.selected ? 1 : 0,
      card && card.dofBucket == null ? -1 : card.dofBucket, pulseBucket, shelfAccentHex(), shelfSettings().bgOpacity
    ].join('|');
  }

  // 重绘单张歌单架卡片的 canvas 贴图。
  function drawCard(card, item) {
    item = item || card.item || {};
    // 绘制签名没有变化时跳过重绘，降低 canvas 和纹理上传成本。
    var nextDrawKey = cardDrawSignature(card, item);
    if (card.drawKey === nextDrawKey) return;
    card.drawKey = nextDrawKey;
    // 当前卡片 canvas、上下文和尺寸。
    var cv = card.canvas, ctx = card.ctx;
    var W = cv.width, H = cv.height;
    ctx.clearRect(0, 0, W, H);
    // 卡片内边距。
    var pad = 18;
    // 当前卡片是否对应正在播放的歌曲。
    var isNow = item.type === 'queue' && item.tag === '正在播放';
    // 当前歌单架视觉设置。
    var shelfLook = shelfSettings();

    // 卡片底
    makeRoundRect(ctx, pad, pad, W - pad*2, H - pad*2, 32);
    // 背景透明度来自歌单架设置。
    ctx.fillStyle = 'rgba(0,0,0,' + shelfLook.bgOpacity.toFixed(3) + ')'; ctx.fill();
    // 轻微玻璃高光渐变。
    var grad = ctx.createLinearGradient(0, 0, W, H);
    grad.addColorStop(0, 'rgba(255,255,255,0.10)');
    grad.addColorStop(1, 'rgba(255,255,255,0.018)');
    ctx.fillStyle = grad; ctx.fill();

    if (isNow) {
      // 正在播放卡片使用强调色和节奏相关描边宽度。
      ctx.strokeStyle = shelfAccentRgba(0.72);
      ctx.lineWidth = 1.8 + Math.sin(uniforms.uTime.value * 3) * 0.28 + bass * 1.2;
    } else {
      // 普通卡片使用低对比描边。
      ctx.strokeStyle = 'rgba(255,255,255,0.14)';
      ctx.lineWidth = 1.1;
    }
    ctx.stroke();

    if (card.selected) {
      // 选中态额外绘制一层带阴影的强调描边。
      ctx.save();
      makeRoundRect(ctx, pad + 2, pad + 2, W - pad*2 - 4, H - pad*2 - 4, 30);
      ctx.shadowColor = shelfAccentRgba(0.58);
      ctx.shadowBlur = 18;
      ctx.strokeStyle = shelfAccentRgba(0.72);
      ctx.lineWidth = 2.2;
      ctx.stroke();
      ctx.restore();
    }

    // 大封面方块
    // 封面区域尺寸。
    var coverSize = H - pad*2 - 8;
    // 封面区域左上角坐标。
    var cx = pad + 6, cy = pad + 4;
    makeRoundRect(ctx, cx, cy, coverSize, coverSize, 26);
    ctx.fillStyle = 'rgba(255,255,255,0.04)'; ctx.fill();
    if (item.cover) {
      // 读取或请求队列封面缓存。
      var rec = playlistCoverCache[item.cover];
      if (rec && rec.loaded && rec.img) {
        // 封面加载完成后裁剪到圆角区域内绘制。
        ctx.save(); makeRoundRect(ctx, cx, cy, coverSize, coverSize, 26); ctx.clip();
        ctx.drawImage(rec.img, cx, cy, coverSize, coverSize); ctx.restore();
      } else if (!rec || (!rec.loading && !rec.failed)) {
        // 尚未加载时发起异步请求，回调里重绘当前卡片。
        requestPlaylistCover(item.cover, function(){ drawCard(card, item); });
      }
    }

    // 文本区
    // 文本区域起始 X 坐标。
    var tx = pad + coverSize + 32;
    ctx.font = '700 17px Inter, Arial';
    ctx.fillStyle = isNow ? shelfAccentRgba(0.92) : 'rgba(255,255,255,0.92)';
    ctx.fillText(item.tag || '', tx, pad + 36);

    // 标题文本，最多两行。
    ctx.font = '700 30px Inter, Arial';
    ctx.fillStyle = 'rgba(255,255,255,0.96)';
    wrapText(ctx, item.title || '', tx, pad + 78, W - tx - pad - 14, 36, 2);

    // 副标题文本，通常是歌手。
    ctx.font = '400 17px Inter, Arial';
    ctx.fillStyle = 'rgba(255,255,255,0.52)';
    wrapText(ctx, item.sub || '', tx, pad + 156, W - tx - pad - 14, 24, 2);

    // 律动进度条
    // 底部短线随 bass 延长，正在播放时使用强调色。
    ctx.strokeStyle = isNow ? shelfAccentRgba(0.90) : 'rgba(255,255,255,0.30)';
    ctx.lineWidth = 3.5;
    ctx.beginPath();
    ctx.moveTo(tx, H - pad - 22);
    ctx.lineTo(tx + Math.min(260, 80 + bass * 320), H - pad - 22);
    ctx.stroke();

    if (card.isCenter) {
      // 中心卡片显示当前可执行动作提示。
      var actionY = H - pad - 78;
      if (item.type === 'playlist') {
        // 在线歌单入口已移除，保留说明。
        ctx.font = '800 14px Inter, "Microsoft YaHei", Arial';
        ctx.fillStyle = 'rgba(255,255,255,0.58)';
        ctx.fillText('在线歌单已移除', tx, actionY + 25);
      } else if (item.type === 'queue') {
        // 队列卡片中心态显示点击播放提示。
        ctx.font = '600 14px Inter, "Microsoft YaHei", Arial';
        ctx.fillStyle = shelfAccentRgba(0.84);
        ctx.fillText('点击播放', tx, actionY + 25);
      }
    }

    // 景深模糊在 canvas 侧用暗层近似，减少 shader 复杂度。
    var dof = card.dofBlur || 0;
    if (dof > 0.12) {
      makeRoundRect(ctx, pad, pad, W - pad*2, H - pad*2, 32);
      ctx.fillStyle = 'rgba(0,0,0,' + Math.min(0.28, dof * 0.18).toFixed(3) + ')';
      ctx.fill();
    }

    // 通知 Three.js 上传更新后的 canvas 纹理。
    card.texture.needsUpdate = true;
  }

  // 构建单张 3D 歌单架卡片。
  function buildOneCard(item, i) {
    // 每张卡片是一张 canvas 贴图加一个平面网格；重绘 canvas 后通过 texture.needsUpdate 推给 GPU。
    // 卡片 canvas。
    var cv = document.createElement('canvas');
    cv.width = 720; cv.height = 360;
    // 卡片绘制上下文。
    var ctx = cv.getContext('2d');
    // 由 canvas 创建的 Three.js 纹理。
    var tx = new THREE.CanvasTexture(cv);
    tx.minFilter = THREE.LinearFilter; tx.magFilter = THREE.LinearFilter;
    tx.generateMipmaps = false;
    // 卡片材质使用透明基础材质，避免参与光照。
    var mat = new THREE.MeshBasicMaterial({ map: tx, transparent: true, opacity: 0.96, depthWrite: false, depthTest: false, side: THREE.DoubleSide });
    // 卡片平面几何尺寸与 canvas 宽高比一致。
    var geo = new THREE.PlaneGeometry(2.05, 1.025, 1, 1);
    // 卡片网格。
    var mesh = new THREE.Mesh(geo, mat);
    mesh.renderOrder = 50 + i;
    // 点击命令写在 userData 中，射线命中后按这里执行。
    mesh.userData.action = item.type === 'queue' ? { kind:'playQueue', index: item.queueIndex } : { kind:'empty' };
    group.add(mesh);
    // 卡片运行期状态。
    var card = { canvas: cv, ctx: ctx, texture: tx, mesh: mesh, item: item, index: i, isCenter: false, selected: i === selectedIdx, floatMix: 0, fxPulse: 0, dofBlur: 0, dofBucket: -1, drawKey: '' };
    return card;
  }

  // 主动预热纹理上传，减少首次显示时的 GPU 上传卡顿。
  function warmTextureUpload(tex) {
    if (!tex || !renderer || typeof renderer.initTexture !== 'function') return;
    try { renderer.initTexture(tex); } catch (e) {}
  }

  // 取消正在分帧构建的卡片队列。
  function cancelCardBuildQueue() {
    if (!cardBuildQueue) return;
    // 标记取消，防止已排队的下一帧继续构建。
    cardBuildQueue.cancelled = true;
    if (cardBuildQueue.raf) cancelAnimationFrame(cardBuildQueue.raf);
    cardBuildQueue = null;
  }

  // 销毁当前窗口内已经渲染的卡片和关联资源。
  function disposeRenderedCards() {
    cancelCardBuildQueue();
    while (group && group.children.length) {
      // 从组中取出一个子对象。
      var ch = group.children.pop();
      // 释放材质和纹理，避免频繁重建窗口造成显存泄漏。
      if (ch.material) { if (ch.material.map) ch.material.map.dispose(); ch.material.dispose(); }
      // 释放几何体资源。
      if (ch.geometry) ch.geometry.dispose();
    }
    // 清空卡片数组。
    cards = [];
    // 标记当前没有有效渲染窗口。
    renderedStart = -1;
  }

  // 将卡片构建任务拆到空闲帧执行。
  function scheduleQueuedCardBuild(job) {
    // 异步建卡每批最多处理少量项目，把 canvas 绘制和纹理上传拆散到空闲帧，减少打开歌单架时的卡顿。
    // 单次空闲帧构建步骤。
    function step(deadline) {
      // 队列被取消或管理器销毁时停止。
      if (!job || job.cancelled || cardBuildQueue !== job || !group) return;
      // 本批开始时间，用于控制单帧耗时。
      var started = performance.now();
      // 本批已构建数量。
      var built = 0;
      while (job.next <= job.end && built < 2 && performance.now() - started < 7) {
        // 构建当前窗口中的下一张卡片。
        var card = buildOneCard(allItems[job.next], job.next);
        cards.push(card);
        drawCard(card, card.item);
        warmTextureUpload(card.texture);
        job.next += 1;
        built += 1;
      }
      if (job.next <= job.end) {
        // 仍有剩余卡片时继续排队到空闲帧或下一帧。
        if (window.requestIdleCallback) {
          requestIdleCallback(step, { timeout: 180 });
        } else {
          job.raf = requestAnimationFrame(step);
        }
      } else {
        // 全部构建完成后清空队列状态。
        cardBuildQueue = null;
      }
    }
    // 优先使用 requestIdleCallback，降级到 RAF。
    if (window.requestIdleCallback) requestIdleCallback(step, { timeout: 180 });
    else job.raf = requestAnimationFrame(step);
  }

  // 同步当前中心卡片附近的渲染窗口。
  function syncRenderedWindow(force, asyncBuild) {
    // 根据 centerTarget 计算当前可见窗口；窗口未变化时只补绘内容变化的卡片，窗口变化时整体重建。
    if (!group) return;
    // 全量条目数。
    var total = allItems.length;
    if (!total) { disposeRenderedCards(); return; }
    // 当前中心索引取整。
    var center = Math.round(centerTarget);
    // 可见窗口起点。
    var start = Math.max(0, center - SHELF_VISIBLE_RADIUS);
    // 可见窗口终点。
    var end = Math.min(total - 1, start + SHELF_MAX_RENDER - 1);
    // 靠近队尾时回推起点，保持窗口尽量满。
    start = Math.max(0, end - SHELF_MAX_RENDER + 1);
    if (!force && start === renderedStart && cards.length === (end - start + 1)) {
      // 窗口未变化时只检查条目引用变化并局部重绘。
      cards.forEach(function(c) {
        // 当前卡片索引对应的新条目。
        var nextItem = allItems[c.index] || c.item;
        if (c.item !== nextItem) {
          c.item = nextItem;
          c.drawKey = '';
          drawCard(c, c.item);
        }
      });
      return;
    }
    // 窗口变化时销毁旧窗口。
    disposeRenderedCards();
    // 记录新窗口起点。
    renderedStart = start;
    if (asyncBuild) {
      // 异步构建队列状态。
      cardBuildQueue = { start:start, end:end, next:start, cancelled:false, raf:0 };
      scheduleQueuedCardBuild(cardBuildQueue);
      return;
    }
    // 同步构建窗口内全部卡片。
    for (var itemIdx = start; itemIdx <= end; itemIdx++) {
      // 构建并绘制单张卡片。
      var card = buildOneCard(allItems[itemIdx], itemIdx);
      cards.push(card);
      drawCard(card, card.item);
    }
  }

  // 重建歌单架当前内容和模式相关附加物。
  function rebuild(asyncCards) {
    // 队列、主题或模式发生变化时重建歌单架；舞台附加物和二级列表会跟随当前模式重新初始化。
    if (!group) return;
    // 先释放当前窗口卡片。
    disposeRenderedCards();
    if (connectorParticles) {
      // 清理舞台连接粒子。
      if (connectorParticles.parent) connectorParticles.parent.remove(connectorParticles);
      if (connectorParticles.geometry) connectorParticles.geometry.dispose();
      if (connectorParticles.material) connectorParticles.material.dispose();
      connectorParticles = null;
    }
    if (floorMirror) {
      // 清理舞台地面倒影。
      if (floorMirror.parent) floorMirror.parent.remove(floorMirror);
      if (floorMirror.geometry) floorMirror.geometry.dispose();
      if (floorMirror.material) floorMirror.material.dispose();
      floorMirror = null;
    }
    // 从当前播放队列重新生成条目。
    allItems = currentItems();
    // 保存新条目签名。
    lastSig = sig(allItems);
    // 让下次 tick 重新计算卡片重绘节流。
    lastCardRedrawAt = -10;
    lastCardPulseBucket = -1;
    // center 起始 = currentIdx (如果是 queue), 否则 0
    if (allItems.length && allItems[0].type === 'queue' && currentIdx >= 0) {
      // 队列模式默认居中到当前播放歌曲。
      centerTarget = Math.min(allItems.length - 1, currentIdx);
      centerSmooth = centerTarget;
      centerIdx = centerTarget;
    } else if (centerTarget >= allItems.length) {
      // 条目减少后把中心索引夹回有效范围。
      centerTarget = Math.max(0, allItems.length - 1);
      centerSmooth = centerTarget;
    }
    // 选中索引越界时清空选中。
    if (selectedIdx >= allItems.length) selectedIdx = -1;
    // 按最新中心同步渲染窗口。
    syncRenderedWindow(true, !!asyncCards);
    if (mode === 'stage') {
      // 舞台模式需要创建粒子连接和倒影等附加物。
      createStageExtras();
    }
  }

  // ====================================================
  //  PSP 弧形布局: 以 centerSmooth 为基准, 卡片绕弧排列
  //  i 距离 center 越远 → 越靠后, 越小, 越淡
  // ====================================================
  // 根据当前模式和中心索引摆放一张卡片。
  function placeCard(card, i, totalCards, modeIs) {
    var delta = card.index - centerSmooth;     // 正=下方, 负=上方
    // 与中心卡片的绝对距离。
    var absD = Math.abs(delta);
    // 隐藏太远的卡 (>4 全隐藏)
    if (absD > SHELF_VISIBLE_RADIUS + 0.5) { card.mesh.visible = false; return; }
    card.mesh.visible = true;
    // 中心附近卡片 renderOrder 更高，保证叠放关系稳定。
    card.mesh.renderOrder = 60 + Math.round((SHELF_VISIBLE_RADIUS + 1 - Math.min(absD, SHELF_VISIBLE_RADIUS + 1)) * 10);
    // 当前指针视差 X。
    var parX = pointerParallax.x || 0;
    // 当前指针视差 Y。
    var parY = pointerParallax.y || 0;
    // 卡片离中心越远，指针视差影响越小。
    var parWeight = Math.max(0, 1 - absD * 0.16);
    // 卡片点击或节奏触发的额外脉冲。
    var pulse = card.fxPulse || 0;
    // 当前响应式布局参数。
    var layout = shelfLayoutProfile();
    // 当前歌单架视觉设置。
    var shelfLook = shelfSettings();
    // 离中心越远景深越强。
    var nextDof = Math.max(0, Math.min(1, (absD - 0.45) / 3.2));
    // 景深分桶，只有桶变化才重绘 canvas。
    var nextDofBucket = Math.round(nextDof * 5);
    if (card.dofBucket !== nextDofBucket) {
      // 写入新的景深状态并触发卡片贴图重绘。
      card.dofBucket = nextDofBucket;
      card.dofBlur = nextDof;
      drawCard(card, card.item);
    }

    if (modeIs === 'side') {
      // 右侧 3D 架: 恢复更靠近、更斜切的打开姿态，让卡片有真正的前后层次。
      // 侧边二级内容是否打开。
      var detailOpenSide = contentList && contentList.isOpen();
      // 当前 shader 时间。
      var nowT = uniforms.uTime.value;
      // 未固定且未打开详情时，用整体可见度驱动轻微呼吸。
      var hoverBreath = (!shelfPinnedOpen && !detailOpenSide) ? shelfVisibility : 0;
      // 常显但未固定时使用更低的渲染层级。
      var passiveAlways = shelfAlwaysVisible() && !shelfPinnedOpen && !detailOpenSide;
      // 选中卡片的浮起目标值。
      var liftTarget = card.selected && !detailOpenSide ? 1 : 0;
      // 浮起和回落使用不同速率。
      var liftRate = liftTarget > (card.floatMix || 0) ? 0.20 : 0.13;
      card.floatMix = (card.floatMix || 0) + (liftTarget - (card.floatMix || 0)) * liftRate;
      if (!liftTarget && card.floatMix < 0.004) card.floatMix = 0;
      // 当前浮起插值。
      var lift = card.floatMix || 0;
      // 侧边层级权重，中心附近更靠前。
      var sideLayer = Math.max(0, SHELF_VISIBLE_RADIUS + 1 - Math.min(absD, SHELF_VISIBLE_RADIUS + 1));
      card.mesh.renderOrder = passiveAlways
        ? (30 + Math.round(sideLayer * 1.1) + Math.round(lift * 96))
        : (60 + Math.round(sideLayer * 10) + Math.round(lift * 70));
      // 侧边悬停呼吸强度。
      var breathPulse = hoverBreath * (0.5 + 0.5 * Math.sin(nowT * 1.22 + card.index * 0.74));
      // 打开动画原始进度。
      var revealRaw = Math.max(0, Math.min(1, (nowT - shelfOpenAnimAt - absD * 0.035) / 0.62));
      // 打开动画平滑进度。
      var reveal = revealRaw * revealRaw * (3 - 2 * revealRaw);
      // 入场偏移强度。
      var entry = (1 - reveal) * (0.82 + absD * 0.075);
      // 二级面板切换动画原始进度。
      var paneRaw = Math.max(0, Math.min(1, (nowT - paneSwitchAt - absD * 0.030) / 0.72));
      // 二级面板切换残余偏移强度。
      var paneEase = 1 - paneRaw * paneRaw * (3 - 2 * paneRaw);
      // 壁纸预设的安全歌单架姿态。
      var wallpaperShelfPose = shouldUseWallpaperSafeShelfCamera();
      // 骷髅预设的安全歌单架姿态。
      var skullShelfPose = shouldUseSkullSafeShelfCamera();
      // 任一安全姿态启用时，减少旋转和位移侵入主视觉。
      var safeShelfPose = wallpaperShelfPose || skullShelfPose;
      // 侧边卡片 X 坐标。
      var px = layout.sideX + absD * layout.sideXStep - (detailOpenSide ? layout.sideDetailShift : 0) + entry * layout.sideEntryX;
      // 侧边卡片 Y 坐标。
      var py = (layout.sideY || 0) - delta * layout.sideYStep + (1 - reveal) * (delta < 0 ? -0.18 : 0.18);
      // 侧边卡片 Z 坐标。
      var pz = layout.sideZ - absD * layout.sideZStep - (1 - reveal) * 0.20;
      // 二级面板切换时给卡片一个横向让位偏移。
      px += paneEase * paneSwitchDir * 0.60;
      py += paneEase * (delta < 0 ? -0.16 : 0.16);
      pz -= paneEase * 0.22;
      // 叠加指针视差。
      px += parX * 0.060 * parWeight;
      py += parY * 0.046 * parWeight;
      pz += (parY * 0.026 - parX * 0.028) * parWeight;
      // 悬停预览时给卡片轻微漂浮。
      py += Math.sin(nowT * 0.92 + card.index * 0.64) * 0.052 * hoverBreath * Math.max(0.20, parWeight);
      pz += Math.cos(nowT * 0.78 + card.index * 0.52) * 0.030 * hoverBreath * parWeight;
      if (lift > 0.001) {
        // 选中卡片略微向用户方向浮起。
        px -= lift * (skullShelfPose ? 0.035 : (layout.portrait ? 0.065 : 0.145));
        py += lift * (skullShelfPose ? 0.045 : (layout.portrait ? 0.075 : 0.105));
        pz += lift * (skullShelfPose ? 0.080 : 0.220);
      }
      // 侧边卡片最终缩放。
      var scale = (absD < 0.5 ? 1.12 : Math.max(0.55, 1.04 - absD * 0.14)) * (0.88 + reveal * 0.12) * (1 + pulse * 0.056 + breathPulse * 0.026 + lift * (skullShelfPose ? 0.045 : 0.075)) * layout.sideScale;
      if (wallpaperShelfPose) scale *= 1.22;
      else if (skullShelfPose) scale *= 1.04;
      card.mesh.position.set(px, py, pz);
      if (skullShelfPose && camera) {
        // 骷髅安全姿态使用相机朝向作为基准，再叠加轻微旋转。
        card.mesh.quaternion.copy(camera.quaternion);
        card.mesh.rotateX(layout.sideRotX - delta * 0.008 - parY * 0.004 * parWeight);
        card.mesh.rotateY(layout.sideRotY + (1 - reveal) * 0.012 + parX * 0.006 * parWeight);
      } else {
        // 普通和壁纸姿态直接写欧拉角。
        var safeRotY = wallpaperShelfPose ? 0.12 : layout.sideRotY;
        var safeEntryRotY = wallpaperShelfPose ? 0.05 : 0.16;
        card.mesh.rotation.y = (safeShelfPose ? safeRotY : layout.sideRotY) + (1 - reveal) * safeEntryRotY + parX * (safeShelfPose ? 0.014 : 0.038) * parWeight;
        var safeRotX = wallpaperShelfPose ? 0.020 : layout.sideRotX;
        card.mesh.rotation.x = -delta * (safeShelfPose ? safeRotX : layout.sideRotX) - parY * (safeShelfPose ? 0.010 : 0.024) * parWeight;
      }
      card.mesh.scale.setScalar(scale);
      // 详情打开时弱化主卡片交互感。
      var disabledByDetail = detailOpenSide;
      // 基于中心距离计算基础透明度。
      var opacity = absD < 0.5 ? 1.0 : Math.max(0.22, 1.0 - absD * 0.30);
      if (disabledByDetail) {
        // 内容打开后原卡片退到背景。
        opacity *= card.index === openCardIdx ? 0.16 : 0.08;
        card.mesh.material.color.setScalar(card.index === openCardIdx ? 0.42 : 0.25);
      } else {
        // 常显状态略微压低亮度，选中浮起时恢复。
        if (passiveAlways) opacity *= 0.92 + lift * 0.08;
        card.mesh.material.color.setScalar(passiveAlways ? (0.96 + lift * 0.04) : 1);
      }
      // v8: 自动隐藏 — shelf 不在 focus 区时整体淡化
      card.mesh.material.opacity = Math.min(1, opacity * (shelfVisibility != null ? shelfVisibility : 1) * reveal * (1 - paneEase * 0.24) + pulse * 0.10 * reveal + breathPulse * 0.035) * shelfLook.opacity;
      setCardCenter(card, absD < 0.5);
    } else {
      // 舞台 PSP: 水平展开 + center 突出, dock 在底部
      // 舞台模式 X 坐标。
      var pxStage = (layout.stageX || 0) + delta * layout.stageXStep;
      // 舞台模式 Y 坐标。
      var pyStage = layout.stageY;
      // 舞台模式 Z 坐标，中心卡更靠前。
      var pzStage = absD < 0.5 ? layout.stageZ : (layout.stageZ - Math.min(2.0, absD) * 0.55);
      // 舞台二级面板切换原始进度。
      var paneRawS = Math.max(0, Math.min(1, (uniforms.uTime.value - paneSwitchAt - absD * 0.030) / 0.72));
      // 舞台二级面板切换残余偏移强度。
      var paneEaseS = 1 - paneRawS * paneRawS * (3 - 2 * paneRawS);
      pxStage += paneEaseS * paneSwitchDir * 0.80;
      pzStage -= paneEaseS * 0.28;
      // 叠加舞台模式指针视差。
      pxStage += parX * 0.110 * parWeight;
      pyStage += parY * 0.060 * parWeight;
      pzStage += (parY * 0.040 - parX * 0.035) * parWeight;
      // 舞台卡片最终缩放。
      var scaleS = (absD < 0.5 ? 1.20 : Math.max(0.45, 1.0 - absD * 0.22)) * (1 + pulse * 0.060) * layout.stageScale;
      card.mesh.position.set(pxStage, pyStage, pzStage);
      card.mesh.rotation.y = -delta * 0.22 + parX * 0.050 * parWeight;
      card.mesh.rotation.x = 0.10 - absD * 0.04 - parY * 0.028 * parWeight;
      card.mesh.scale.setScalar(scaleS);
      // 舞台详情打开状态。
      var disabledStage = contentList && contentList.isOpen();
      // 舞台卡片基础透明度。
      var opS = absD < 0.5 ? 1.0 : Math.max(0.18, 1.0 - absD * 0.32);
      if (disabledStage) {
        // 详情打开后舞台卡片退到背景。
        opS *= card.index === openCardIdx ? 0.16 : 0.08;
        card.mesh.material.color.setScalar(card.index === openCardIdx ? 0.42 : 0.25);
      } else {
        card.mesh.material.color.setScalar(1);
      }
      card.mesh.material.opacity = Math.min(1, opS * (shelfVisibility != null ? shelfVisibility : 1) * (1 - paneEaseS * 0.24) + pulse * 0.10) * shelfLook.opacity;
      setCardCenter(card, absD < 0.5);
    }
  }

  // 同步卡片是否为中心态，并在状态变化时重绘贴图。
  function setCardCenter(card, isCenter) {
    if (card.isCenter !== isCenter) {
      card.isCenter = isCenter;
      drawCard(card, card.item);
    } else {
      card.isCenter = isCenter;
    }
  }

  // 处理在线歌单卡片点击；当前版本该功能已移除。
  function playPlaylistCard(card) {
    // 即使功能移除，也保留一次卡片脉冲作为点击反馈。
    if (card) pulseCard(card, 1.05);
    showToast('在线歌单功能已移除');
    return true;
  }

  // 给卡片施加一次可衰减的视觉脉冲。
  function pulseCard(card, amount) {
    if (!card) return;
    pulseObjectValue(card, 'fxPulse', amount || 1, 0.46);
  }

  // 创建舞台模式专用的连接粒子和底部倒影。
  function createStageExtras() {
    if (!group) return;
    // 连接粒子数量。
    var pcount = 80;
    // 连接粒子几何体。
    var pgeo = new THREE.BufferGeometry();
    // 粒子位置数组。
    var ppos = new Float32Array(pcount * 3);
    // 粒子颜色数组。
    var pcol = new Float32Array(pcount * 3);
    // 粒子随机种子数组。
    var prnd = new Float32Array(pcount);
    for (var i = 0; i < pcount; i++) {
      // 粒子在舞台底部附近随机散布。
      ppos[i*3] = (Math.random() - 0.5) * 6;
      ppos[i*3+1] = (Math.random() - 0.5) * 1.2 + 0.3;
      ppos[i*3+2] = 1.0 + Math.random() * 1.5;
      // 使用偏青色的连接粒子。
      pcol[i*3] = 0.56; pcol[i*3+1] = 0.91; pcol[i*3+2] = 1.0;
      // 每个粒子保存一个随机相位。
      prnd[i] = Math.random();
    }
    // 写入粒子几何属性。
    pgeo.setAttribute('position', new THREE.BufferAttribute(ppos, 3));
    pgeo.setAttribute('aColor',   new THREE.BufferAttribute(pcol, 3));
    pgeo.setAttribute('aRand',    new THREE.BufferAttribute(prnd, 1));
    // 舞台连接粒子材质，直接使用 uTime 驱动漂浮。
    var pmat = new THREE.ShaderMaterial({
      uniforms:{ uTime: uniforms.uTime, uPixel: uniforms.uPixel, uDotTex: uniforms.uDotTex },
      vertexShader:`precision highp float; uniform float uTime, uPixel; attribute vec3 aColor; attribute float aRand;
varying vec3 vC; varying float vA;
void main(){
  vec3 p = position;
  p.x += sin(uTime * 0.4 + aRand * 6.0) * 1.5;
  p.y += sin(uTime * 0.6 + aRand * 4.0) * 0.2;
  p.z += cos(uTime * 0.5 + aRand * 5.0) * 0.4;
  vC = aColor; vA = 0.4 + 0.4 * sin(uTime * 1.5 + aRand * 7.0);
  vec4 m = modelViewMatrix * vec4(p, 1.0);
  gl_PointSize = 4.0 * uPixel;
  gl_Position = projectionMatrix * m;
}`,
      fragmentShader:`precision highp float; uniform sampler2D uDotTex;
varying vec3 vC; varying float vA;
void main(){ vec4 t = texture2D(uDotTex, gl_PointCoord); if (t.a < 0.02) discard; gl_FragColor = vec4(vC, t.a * vA); }`,
      transparent:true, depthWrite:false, blending: THREE.AdditiveBlending,
    });
    // 连接粒子点云对象。
    connectorParticles = new THREE.Points(pgeo, pmat);
    connectorParticles.frustumCulled = false;
    connectorParticles.renderOrder = 49;
    connectorParticles.position.set(0, -2.2, 0);
    // 粒子挂到歌单架同级，避免继承卡片组的全部变换。
    if (group.parent) group.parent.add(connectorParticles); else scene.add(connectorParticles);
    // 底部地面反射
    // 倒影平面几何。
    var mGeo = new THREE.PlaneGeometry(10, 1.8);
    // 倒影渐变贴图 canvas。
    var mCanvas = document.createElement('canvas'); mCanvas.width = 256; mCanvas.height = 64;
    // 倒影 canvas 绘制上下文。
    var mctx = mCanvas.getContext('2d');
    // 从上到下淡出的白色渐变。
    var mg = mctx.createLinearGradient(0, 0, 0, 64);
    mg.addColorStop(0, 'rgba(255,255,255,0.07)'); mg.addColorStop(1, 'rgba(255,255,255,0)');
    mctx.fillStyle = mg; mctx.fillRect(0, 0, 256, 64);
    // 倒影贴图。
    var mTex = new THREE.CanvasTexture(mCanvas);
    mTex.generateMipmaps = false;
    // 倒影材质。
    var mMat = new THREE.MeshBasicMaterial({ map: mTex, transparent:true, depthWrite:false, opacity:0.55 });
    // 倒影网格。
    floorMirror = new THREE.Mesh(mGeo, mMat);
    floorMirror.position.set(0, -2.85, 0.4);
    floorMirror.rotation.x = -Math.PI / 2;
    // 倒影同样挂到歌单架同级。
    if (group.parent) group.parent.add(floorMirror); else scene.add(floorMirror);
  }

  // 生成当前歌单架内容签名，用于判断是否需要重建。
  function sig(items) {
    // 未传入条目时，根据播放队列构造轻量签名条目。
    items = items || playQueue.map(function(song, idx){
      return { type:'queue', title: song.name, queueIndex: idx };
    });
    // 只采样首尾少量条目，避免长队列每次拼接过大字符串。
    var sample = items.slice(0, 3).concat(items.slice(Math.max(3, items.length - 3)));
    return ['queue', items.length, currentIdx, sample.map(function(it){ return [it.type, it.playlistId||'', it.queueIndex||'', it.title||''].join('|'); }).join('||')].join('::');
  }

  // 应用当前选中索引，并刷新受影响卡片。
  function applySelectedIndex(idx) {
    // 选中索引归一化，负数表示无选中。
    idx = idx == null || idx < 0 ? -1 : Math.round(idx);
    selectedIdx = idx;
    cards.forEach(function(c) {
      // 当前卡片是否应进入选中态。
      var next = c.index === selectedIdx;
      if (c.selected !== next) {
        c.selected = next;
        drawCard(c, c.item);
      }
    });
  }

  // 歌单架中心卡片按方向步进。
  function step(direction) {
    if (!allItems.length) return;
    // 步进前的目标中心索引。
    var prevTarget = Math.round(centerTarget);
    // 夹紧到条目范围内的新目标中心索引。
    centerTarget = Math.max(0, Math.min(allItems.length - 1, centerTarget + direction));
    // 步进后的目标中心索引。
    var nextTarget = Math.round(centerTarget);
    // 中心变化可能跨出当前窗口，需要同步渲染窗口。
    syncRenderedWindow(false);
    // 选中步进后的中心卡片。
    applySelectedIndex(nextTarget);
    // 实际变化时播放选择反馈。
    if (nextTarget !== prevTarget) playShelfSelectTick(direction, 'card');
    // 给目标卡片一次轻脉冲。
    pulseCard(cards.find(function(c){ return c.index === nextTarget; }), 0.55);
  }

  // 用屏幕坐标粗略命中一张 3D 卡片的投影矩形。
  function screenHitCard(card, sx, sy, pad) {
    // 无效、不可见或管理器未显示时不命中。
    if (!card || !card.mesh || !card.mesh.visible || !group || !group.visible) return null;
    // 读取平面几何尺寸。
    var params = card.mesh.geometry && card.mesh.geometry.parameters || {};
    // 半宽。
    var hw = (params.width || 1.7) / 2;
    // 半高。
    var hh = (params.height || 0.85) / 2;
    // 卡片四角本地坐标。
    var pts = [
      new THREE.Vector3(-hw, -hh, 0),
      new THREE.Vector3( hw, -hh, 0),
      new THREE.Vector3( hw,  hh, 0),
      new THREE.Vector3(-hw,  hh, 0),
    ];
    // 投影后的屏幕包围盒。
    var minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
    card.mesh.updateMatrixWorld(true);
    for (var i = 0; i < pts.length; i++) {
      // 世界坐标投影到 NDC，再转成屏幕像素坐标。
      pts[i].applyMatrix4(card.mesh.matrixWorld).project(camera);
      var x = (pts[i].x + 1) * innerWidth / 2;
      var y = (1 - pts[i].y) * innerHeight / 2;
      minX = Math.min(minX, x); maxX = Math.max(maxX, x);
      minY = Math.min(minY, y); maxY = Math.max(maxY, y);
    }
    // 命中扩展边距，便于侧边卡片点击。
    pad = pad == null ? 28 : pad;
    if (sx < minX - pad || sx > maxX + pad || sy < minY - pad || sy > maxY + pad) return null;
    // 计算近似 UV，供后续区分卡片内区域。
    var u = clampRange((sx - minX) / Math.max(1, maxX - minX), 0, 1);
    var v = 1 - clampRange((sy - minY) / Math.max(1, maxY - minY), 0, 1);
    return { x: u, y: v };
  }

  // 按屏幕坐标从前到后拾取一张歌单架卡片。
  function pickCardAtScreen(sx, sy, pad) {
    // 无卡片或歌单架不可见时无法拾取。
    if (!cards.length || !group || !group.visible) return null;
    // 按 renderOrder 从前到后排序，优先命中视觉最前面的卡。
    var ordered = cards.slice().sort(function(a, b){ return (b.mesh.renderOrder || 0) - (a.mesh.renderOrder || 0); });
    for (var i = 0; i < ordered.length; i++) {
      // 使用扩展边距做屏幕矩形命中。
      var uv = screenHitCard(ordered[i], sx, sy, pad == null ? 72 : pad);
      if (uv) return { card: ordered[i], uv: uv, screenPick: true };
    }
    return null;
  }

  // 暴露给外部的歌单架控制接口。
  return {
    // 切换歌单架模式，并按需创建或销毁 Three.js 组。
    setMode: function(m) {
      if (m === mode && group) return;
      mode = m;
      if (m === 'off') {
        // 关闭模式下释放卡片和舞台附加资源。
        if (group) { scene.remove(group); cards.forEach(function(c){ c.texture.dispose(); c.mesh.material.dispose(); c.mesh.geometry.dispose(); }); }
        if (connectorParticles) { scene.remove(connectorParticles); connectorParticles.geometry.dispose(); connectorParticles.material.dispose(); connectorParticles = null; }
        if (floorMirror) { scene.remove(floorMirror); floorMirror.geometry.dispose(); floorMirror.material.dispose(); floorMirror = null; }
        group = null; cards = [];
        if (contentList) contentList.close();
        return;
      }
      if (!group) {
        // 首次启用时创建歌单架根组。
        group = new THREE.Group();
        group.renderOrder = 50;
        scene.add(group);
      }
      // 模式切换后同步重建卡片和附加物。
      rebuild(false);
    },
    // 获取当前歌单架模式。
    getMode: function(){ return mode; },
    // 每帧更新歌单架动画、显隐和内容刷新。
    update: function(dt) {
      if (!group) return;
      // PSP 滚动平滑
      centerSmooth += (centerTarget - centerSmooth) * 0.16;
      if (Math.abs(centerSmooth - centerTarget) < 0.001) centerSmooth = centerTarget;
      // 当前指针视差。
      var px = pointerParallax.x, py = pointerParallax.y;
      // 悬停提示显隐进度。
      var cueVis = tickShelfHoverCue(dt);
      // 侧栏只在右侧停留时淡入。
      // 本帧目标可见度。
      var targetVis;
      if (mode === 'side') {
        // 二级内容打开状态。
        var contentOpen = contentList && contentList.isOpen();
        if (!allItems.length && !contentOpen) targetVis = 0;
        else targetVis = (contentOpen || shelfPinnedOpen || shelfAlwaysVisible()) ? 1.0 : (cueVis > 0.01 ? Math.max(0.16, cueVis * 0.88) : 0);
      } else {
        targetVis = allItems.length ? 1.0 : 0;
      }
      // 平滑逼近目标可见度。
      shelfVisibility += (targetVis - shelfVisibility) * (targetVis > shelfVisibility ? 0.22 : 0.18);
      if (shelfVisibility < 0.01 && targetVis === 0) shelfVisibility = 0;
      // 根组可见性同时受启动揭示、模式和内容状态控制。
      group.visible = isShelfAppRevealed() && (mode !== 'side' || shelfVisibility > 0) && (allItems.length > 0 || (contentList && contentList.isOpen()));
      if (connectorParticles) connectorParticles.visible = group.visible && mode === 'stage';
      if (floorMirror) floorMirror.visible = group.visible && mode === 'stage';
      if (mode === 'side') {
        // 常显但未固定时，组层级更低，避免抢占主视觉。
        var passiveAlwaysGroup = shelfAlwaysVisible() && !shelfPinnedOpen && !(contentList && contentList.isOpen());
        // 有卡片浮起时临时提高层级。
        var liftedCardActive = passiveAlwaysGroup && cards.some(function(c){ return c.selected || (c.floatMix || 0) > 0.025; });
        group.renderOrder = passiveAlwaysGroup && !liftedCardActive ? 30 : 50;
        group.position.set(0, 0, 0);
        // 常显歌单架可轻微绑定主封面旋转。
        var bindToCover = shelfAlwaysVisible() && particles && particles.rotation && !(contentList && contentList.isOpen());
        if (bindToCover) {
          group.rotation.x += ((particles.rotation.x - py * 0.010) - group.rotation.x) * 0.075;
          group.rotation.y += ((particles.rotation.y + px * 0.018) - group.rotation.y) * 0.075;
          group.rotation.z += (particles.rotation.z - group.rotation.z) * 0.075;
        } else {
          group.rotation.y += ((px * 0.018) - group.rotation.y) * 0.045;
          group.rotation.x += ((-py * 0.010) - group.rotation.x) * 0.045;
          group.rotation.z += (0 - group.rotation.z) * 0.045;
        }
      } else {
        // 舞台模式让整组有轻微漂浮和指针视差。
        group.renderOrder = 50;
        var t = uniforms.uTime.value;
        group.position.y = Math.sin(t * 0.3) * 0.04;
        group.position.x = px * 0.10;
        group.rotation.y = px * 0.025;
        group.rotation.x = -py * 0.012;
      }
      // 逐张摆放卡片。
      for (var i = 0; i < cards.length; i++) {
        placeCard(cards[i], i, cards.length, mode);
      }
      // 内容更新 (节流)
      // 卡片文字、封面和节拍光效不用每帧重绘，节流后只在签名变化或脉冲桶变化时刷新贴图。
      if (uniforms.uTime.value - lastUpdate > 0.8) {
        lastUpdate = uniforms.uTime.value;
        // 当前内容签名。
        var nextSig = sig();
        if (nextSig !== lastSig) rebuild();
        else {
          // 节奏脉冲分桶，用于节流卡片重绘。
          var pulseBucket = Math.round((bass + beatPulse * 0.85) * 10);
          // 播放中刷新更频繁，暂停时降低频率。
          var redrawInterval = playing ? 1.35 : 4.0;
          if (pulseBucket !== lastCardPulseBucket || uniforms.uTime.value - lastCardRedrawAt > redrawInterval) {
            lastCardPulseBucket = pulseBucket;
            lastCardRedrawAt = uniforms.uTime.value;
            cards.forEach(function(c){
              // 同步条目引用和中心态，必要时重绘。
              c.item = allItems[c.index] || c.item;
              c.isCenter = Math.abs(c.index - centerSmooth) < 0.5;
              if (c.isCenter || c.dofBucket <= 1 || c.index === currentIdx) drawCard(c, c.item);
            });
          }
        }
      }
      // 二级内容框 update
      if (contentList) contentList.update(dt);
    },
    // 当前封面变化后触发歌单架重建，刷新队列卡封面。
    onCoverChange: function() {
      if (group && mode !== 'off' && uniforms.uTime.value - lastUpdate > 0.2) {
        lastUpdate = uniforms.uTime.value;
        rebuild();
      }
    },
    // 暴露重建函数给安全包装和外部调度器。
    rebuild: rebuild,
    // 刷新主题相关绘制，例如强调色和背景透明度。
    refreshTheme: function() {
      cards.forEach(function(c) {
        c.drawKey = '';
        drawCard(c, c.item);
      });
      if (contentList && contentList.refreshTheme) contentList.refreshTheme();
    },
    // 使用 Three.js 射线拾取可见卡片。
    raycastCards: function(raycaster) {
      if (!group || !group.visible || !cards.length) return null;
      // 只把可见 mesh 交给射线检测。
      var visibleMeshes = cards.filter(function(c){ return c.mesh.visible; }).map(function(c){ return c.mesh; });
      // 射线命中结果。
      var hits = raycaster.intersectObjects(visibleMeshes, false);
      if (!hits.length) return null;
      // 命中的卡片状态对象。
      var card = cards.find(function(c){ return c.mesh === hits[0].object; });
      return { card: card, point: hits[0].point, uv: hits[0].uv };
    },
    // 屏幕坐标拾取卡片。
    pickCardAtScreen: pickCardAtScreen,
    // PSP 步进
    // 移到下一张卡。
    next: function() { step(1); },
    // 移到上一张卡。
    prev: function() { step(-1); },
    // 按给定方向滚动。
    scrollBy: function(d) { step(d); },
    // 获取当前中心卡片索引。
    getCenterIdx: function() { return Math.round(centerSmooth); },
    // 获取指定索引对应的已渲染卡片。
    getCardAt: function(idx) { return cards.find(function(c){ return c.index === idx; }); },
    // 获取当前已渲染卡片数组。
    getCards: function() { return cards; },
    // 播放指定索引的在线歌单卡片；当前只保留移除提示。
    playPlaylistAt: function(idx) {
      return playPlaylistCard(cards.find(function(c){ return c.index === idx; }));
    },
    // 清空当前选中卡片。
    clearSelected: function() {
      applySelectedIndex(-1);
    },
    // 设置当前选中卡片。
    setSelected: function(idx) {
      applySelectedIndex(idx);
    },
    // 执行卡片 userData 中记录的动作。
    triggerAction: function(action) {
      if (!action) return;
      // 找到动作对应的卡片用于反馈。
      var card = cards.find(function(c) { return c.mesh.userData.action === action; });
      pulseCard(card, action.kind === 'loadPlaylist' ? 1.0 : 0.70);
      if (action.kind === 'playQueue') {
        // 队列卡片直接播放指定队列项。
        playQueueAt(action.index);
      } else if (action.kind === 'loadPlaylist') {
        // 在线歌单动作保留内容框入口兼容旧结构。
        if (!contentList) contentList = makeContentListManager();
        openCardIdx = card ? card.index : -1;
        contentList.open(action.playlistId, action.title || (card && card.item.title), card);
        setShelfPinnedOpen(true, true);
        if (typeof setFocusZone === 'function') setFocusZone('shelf-detail', true);
      } else if (action.kind === 'empty') {
        // 空卡片打开普通播放列表面板。
        togglePlaylistPanel(true);
      }
    },
    // 二级内容框 open/close
    // 打开指定卡片的二级内容，或对队列卡片直接播放。
    openContent: function(cardIdx) {
      // 查找目标卡片。
      var card = cards.find(function(c){ return c.index === cardIdx; });
      if (!card) return;
      // 卡片动作描述。
      var action = card.mesh.userData.action;
      if (!action) return;
      pulseCard(card, 1.0);
      // queue 类型 → 直接播放, 不需要内容框
      if (action.kind === 'playQueue') {
        playQueueAt(action.index);
        return;
      }
      if (action.kind === 'loadPlaylist') {
        // 在线歌单内容列表兼容旧逻辑。
        if (!contentList) contentList = makeContentListManager();
        openCardIdx = card.index;
        contentList.open(action.playlistId, action.title || card.item.title, card);
        setShelfPinnedOpen(true, true);
        if (typeof setFocusZone === 'function') setFocusZone('shelf-detail', true);
      }
      if (action.kind === 'empty') togglePlaylistPanel(true);
    },
    // 关闭二级内容框。
    closeContent: function() {
      // 清空打开卡片索引。
      openCardIdx = -1;
      if (contentList) contentList.close();
      // 恢复主提示显隐。
      var hint = document.getElementById('hint');
      if (hint) hint.classList.toggle('shelf-hidden', shelfPinnedOpen);
      // 焦点区回到侧边歌单架或主视觉。
      if (typeof setFocusZone === 'function') setFocusZone(shelfPinnedOpen ? 'shelf-side' : null, true);
    },
    // 判断是否有二级内容打开。
    hasOpenContent: function() { return contentList && contentList.isOpen(); },
    // 获取二级内容管理器。
    getContentList: function() { return contentList; },
    // 获取当前打开二级内容的卡片索引。
    getOpenContentIndex: function() { return openCardIdx; },
    // 当前歌单架是否可交互。
    canInteract: function() { return mode !== 'off' && allItems.length > 0; }
  };
}
// 创建全局歌单架管理器实例。
shelfManager = makeShelfManager();
// 安全重建歌单架，捕获异常避免影响主播放流程。
function safeShelfRebuild(reason, asyncCards) {
  if (!shelfManager || typeof shelfManager.rebuild !== 'function') return false;
  try {
    shelfManager.rebuild(asyncCards);
    return true;
  } catch (e) {
    console.warn('[ShelfRebuild]', reason || 'unknown', e);
    return false;
  }
}
// 延迟重建歌单架的调度状态。
var deferredShelfRebuild = { raf: 0, reason: '', asyncCards: true, token: 0 };
// 延迟调度歌单架重建，把重活放到 UI 预热任务中执行。
function scheduleShelfRebuild(reason, asyncCards) {
  // 记录最近一次重建原因。
  deferredShelfRebuild.reason = reason || deferredShelfRebuild.reason || 'deferred';
  // 默认使用异步建卡。
  deferredShelfRebuild.asyncCards = asyncCards !== false;
  // token 用于让旧调度失效。
  deferredShelfRebuild.token += 1;
  // 当前调度 token。
  var token = deferredShelfRebuild.token;
  if (deferredShelfRebuild.raf) cancelAnimationFrame(deferredShelfRebuild.raf);
  deferredShelfRebuild.raf = requestAnimationFrame(function(){
    deferredShelfRebuild.raf = 0;
    scheduleUiWarmTask(function(){
      // 只有最新调度可以执行。
      if (token !== deferredShelfRebuild.token) return;
      safeShelfRebuild(deferredShelfRebuild.reason, deferredShelfRebuild.asyncCards);
    }, 260);
  });
}
// 安全关闭歌单架二级内容。
function safeShelfCloseContent(reason) {
  if (!shelfManager || typeof shelfManager.closeContent !== 'function') return false;
  try {
    shelfManager.closeContent();
    return true;
  } catch (e) {
    console.warn('[ShelfCloseContent]', reason || 'unknown', e);
    return false;
  }
}
// 判断播放队列面板是否处于需要渲染的可见状态。
function isPlaylistPanelVisibleForRender() {
  // 播放列表 DOM 面板。
  var panel = document.getElementById('playlist-panel');
  // 面板是否通过任一可见类显示。
  var panelOpen = panel && (panel.classList.contains('show') || panel.classList.contains('peek') || panel.classList.contains('pinned'));
  return !!(panelOpen || miniQueueOpen);
}
// 安全渲染播放队列面板，隐藏时可延迟。
function safeRenderQueuePanel(reason, opts) {
  opts = opts || {};
  if (!isPlaylistPanelVisibleForRender() && opts.deferWhenHidden !== false) {
    // 面板不可见时只标脏，等下次显示再刷新。
    queuePanelDirty = true;
    return true;
  }
  try {
    renderQueuePanel(opts);
    queuePanelDirty = false;
    return true;
  } catch (e) {
    console.warn('[QueuePanelRender]', reason || 'unknown', e);
    return false;
  }
}
// 刷新此前因面板隐藏而延迟的队列渲染。
function flushDeferredQueuePanel(reason) {
  if (!queuePanelDirty) return;
  safeRenderQueuePanel(reason || 'flush-deferred-queue', { animate: false, scrollCurrent: miniQueueOpen, deferWhenHidden: false });
}
// 安全切换播放列表面板标签。
function safeSwitchPlaylistTab(tab, reason) {
  try {
    switchPlaylistTab(tab);
    return true;
  } catch (e) {
    console.warn('[PlaylistTabSwitch]', reason || tab || 'unknown', e);
    return false;
  }
}
// 窗口失焦时清理歌单架预览状态。
window.addEventListener('blur', clearShelfPreviewOnPointerExit);
// 鼠标离开文档时清理歌单架预览状态。
document.addEventListener('mouseleave', clearShelfPreviewOnPointerExit);
// 兼容部分浏览器只触发 mouseout 的离开文档场景。
document.addEventListener('mouseout', function(e) {
  if (!e.relatedTarget && !e.toElement) clearShelfPreviewOnPointerExit();
});

// ============================================================
//  二级内容框 (旧在线歌单内容已移除) — 同样 PSP 风格滚动
// ============================================================
// 创建歌单架二级内容列表管理器。
function makeContentListManager() {
  // 二级内容 Three.js 根组。
  var group = null;
  // 当前渲染的歌曲行卡片。
  var rows = [];           // 每行一张卡 (歌曲)
  // 背景面板对象。
  var panel = null;
  // 二级内容中的完整歌曲列表。
  var allTracks = [];
  // 当前行渲染窗口起点。
  var renderedStart = -1;
  // 二级内容可见行半径。
  var CONTENT_VISIBLE_RADIUS = 5;
  // 二级内容最多渲染行数。
  var CONTENT_MAX_RENDER = CONTENT_VISIBLE_RADIUS * 2 + 1;
  // 二级内容是否打开。
  var open = false;
  // 内容列表目标中心和实际平滑中心。
  var centerTarget = 0, centerSmooth = 0;
  // 当前二级内容标题。
  var playlistTitle = '';
  // 打开二级内容的来源卡片。
  var sourceCard = null;
  // 异步请求 token，用于防止旧请求回写。
  var requestToken = 0;
  // 打开动画起始时间。
  var openAnimAt = -10;
  // 行动画起始时间。
  var rowAnimAt = -10;
  // 面板和行的脏标记。
  var panelDirty = true, rowsDirty = true;
  // 最近面板和行绘制时间。
  var panelDrawAt = -10, rowDrawAt = -10;
  // 加载态动画刷新间隔。
  var LOADING_ANIM_INTERVAL = 1 / 30;
  // 二级内容默认布局参数。
  var DETAIL_BASE = { x: 1.28, y: 0.18, z: 1.36, rx: -0.008, ry: 0.020 };
  // 获取当前二级内容布局，优先使用歌单架响应式布局。
  function detailLayout() {
    return shelfLayoutProfile().detail || DETAIL_BASE;
  }

  // 在 canvas 中创建圆角矩形路径。
  function makeRoundRect(ctx, x, y, w, h, r) {
    ctx.beginPath();
    ctx.moveTo(x+r,y); ctx.arcTo(x+w,y,x+w,y+h,r); ctx.arcTo(x+w,y+h,x,y+h,r);
    ctx.arcTo(x,y+h,x,y,r); ctx.arcTo(x,y,x+w,y,r); ctx.closePath();
  }
  // 将文本缩短到指定宽度，超出时追加省略号。
  function ellipsize(ctx, text, maxWidth) {
    text = String(text || '');
    if (ctx.measureText(text).width <= maxWidth) return text;
    // 逐字符裁剪直到省略号也能放入宽度。
    var out = text;
    while (out.length > 1 && ctx.measureText(out + '...').width > maxWidth) out = out.slice(0, -1);
    return out + '...';
  }
  // 获取 canvas 绘制用强调色。
  function canvasAccent(alpha, fallback) {
    return shelfAccentRgba(alpha, fallback);
  }

  // 确保二级内容背景面板已创建。
  function ensurePanel() {
    if (panel || !group) return;
    // 面板 canvas。
    var cv = document.createElement('canvas');
    cv.width = 900; cv.height = 1024;
    // 面板 canvas 纹理。
    var tx = new THREE.CanvasTexture(cv);
    tx.minFilter = THREE.LinearFilter; tx.magFilter = THREE.LinearFilter;
    tx.generateMipmaps = false;
    // 面板材质。
    var mat = new THREE.MeshBasicMaterial({ map:tx, transparent:true, opacity:0.86, depthWrite:false, depthTest:false, side:THREE.DoubleSide });
    // 面板平面几何。
    var geo = new THREE.PlaneGeometry(2.62, 3.02, 1, 1);
    // 面板网格。
    var mesh = new THREE.Mesh(geo, mat);
    mesh.position.set(-0.02, 0.0, 0.20);
    mesh.renderOrder = 232;
    group.add(mesh);
    // 保存面板运行期对象。
    panel = { canvas:cv, texture:tx, mesh:mesh };
  }

  // 绘制二级内容背景面板。
  function drawPanel() {
    ensurePanel();
    if (!panel) return;
    // 面板 canvas 上下文。
    var ctx = panel.canvas.getContext('2d');
    // 面板画布尺寸。
    var W = panel.canvas.width, H = panel.canvas.height;
    ctx.clearRect(0, 0, W, H);
    makeRoundRect(ctx, 24, 28, W - 48, H - 56, 34);
    // 背景渐变。
    var bg = ctx.createLinearGradient(0, 0, W, H);
    // 面板背景透明度来自歌单架设置。
    var panelBgAlpha = shelfSettings().bgOpacity;
    bg.addColorStop(0, 'rgba(0,0,0,' + Math.min(0.98, panelBgAlpha + 0.02).toFixed(3) + ')');
    bg.addColorStop(0.42, 'rgba(0,0,0,' + panelBgAlpha.toFixed(3) + ')');
    bg.addColorStop(1, 'rgba(0,0,0,' + Math.max(0.20, panelBgAlpha - 0.04).toFixed(3) + ')');
    ctx.fillStyle = bg; ctx.fill();
    ctx.strokeStyle = 'rgba(255,255,255,0.16)';
    ctx.lineWidth = 1.4;
    ctx.stroke();
    ctx.font = '800 38px Inter, "Microsoft YaHei", Arial';
    ctx.fillStyle = 'rgba(255,246,220,0.94)';
    ctx.fillText(ellipsize(ctx, playlistTitle || '队列详情', W - 310), 72, 92);
    ctx.font = '500 18px Inter, "Microsoft YaHei", Arial';
    ctx.fillStyle = canvasAccent(0.62);
    // 可播放歌曲数量。
    var playableCount = allTracks.filter(function(song){ return song && song.id; }).length;
    // 当前是否为加载占位内容。
    var isLoading = allTracks.length === 1 && isLoadingLabel(allTracks[0] && allTracks[0].name);
    // 歌曲数量或加载/空态文案。
    var countLabel = playableCount ? (playableCount + ' 首歌曲') : (isLoading ? '正在载入' : '暂无可播放歌曲');
    ctx.fillText(countLabel, 74, 128);
    // 来源卡片封面地址。
    var coverUrl = sourceCard && sourceCard.item && sourceCard.item.cover;
    // 右上角封面尺寸和位置。
    var coverSize = 96, coverX = W - 172, coverY = 56;
    makeRoundRect(ctx, coverX, coverY, coverSize, coverSize, 22);
    ctx.fillStyle = 'rgba(255,255,255,0.06)';
    ctx.fill();
    if (coverUrl) {
      // 封面缓存。
      var coverRec = playlistCoverCache[coverUrl];
      if (coverRec && coverRec.loaded && coverRec.img) {
        // 封面可用时裁剪到圆角区域。
        ctx.save();
        makeRoundRect(ctx, coverX, coverY, coverSize, coverSize, 22);
        ctx.clip();
        ctx.drawImage(coverRec.img, coverX, coverY, coverSize, coverSize);
        ctx.restore();
      } else if (!coverRec || (!coverRec.loading && !coverRec.failed)) {
        // 封面未加载时异步请求，完成后重绘面板。
        requestPlaylistCover(coverUrl, function(){ drawPanel(); });
      }
    }
    // 顶部分割线高光扫动进度。
    var sweep = (Math.sin((uniforms.uTime.value || 0) * 1.7) + 1) * 0.5;
    // 分割线渐变。
    var shine = ctx.createLinearGradient(70, 154, W - 80, 154);
    shine.addColorStop(0, canvasAccent(0));
    shine.addColorStop(Math.max(0.01, sweep * 0.72), canvasAccent(0.14));
    shine.addColorStop(Math.min(0.99, sweep * 0.72 + 0.14), canvasAccent(0.56));
    shine.addColorStop(1, canvasAccent(0));
    ctx.fillStyle = shine;
    ctx.fillRect(72, 154, W - 144, 2);
    // 标记面板纹理需要上传。
    panel.texture.needsUpdate = true;
  }

  // 释放一个二级内容面板对象。
  function disposePanelObject(targetPanel) {
    if (!targetPanel) return;
    // 从场景中移除 mesh。
    if (targetPanel.mesh && targetPanel.mesh.parent) targetPanel.mesh.parent.remove(targetPanel.mesh);
    // 释放纹理。
    if (targetPanel.texture) targetPanel.texture.dispose();
    // 释放材质。
    if (targetPanel.mesh && targetPanel.mesh.material) targetPanel.mesh.material.dispose();
    // 释放几何体。
    if (targetPanel.mesh && targetPanel.mesh.geometry) targetPanel.mesh.geometry.dispose();
  }

  // 释放当前二级内容面板。
  function disposePanel() {
    disposePanelObject(panel);
    panel = null;
  }

  // 判断文本是否为加载占位。
  function isLoadingLabel(text) {
    return /加载中|正在载入/.test(String(text || ''));
  }

  // 判断当前二级内容是否只有加载占位。
  function isLoadingContent() {
    return allTracks.length === 1 && isLoadingLabel(allTracks[0] && allTracks[0].name);
  }

  // 在面板脏或加载动画需要刷新时绘制面板。
  function drawPanelIfNeeded(force, nowT) {
    nowT = nowT == null ? (uniforms.uTime.value || 0) : nowT;
    if (!force && !panelDirty && (!isLoadingContent() || nowT - panelDrawAt < LOADING_ANIM_INTERVAL)) return;
    drawPanel();
    panelDirty = false;
    panelDrawAt = nowT;
  }

  // 绘制二级内容中的一行歌曲卡片。
  function drawRow(row, song, isCenter) {
    // 行 canvas 和上下文。
    var cv = row.canvas, ctx = cv.getContext('2d');
    // 行画布尺寸。
    var W = cv.width, H = cv.height;
    // 是否具备可播放歌曲 id。
    var playable = !!(song && song.id);
    // 当前行动作是否可用。
    var actionReady = playable;
    ctx.clearRect(0, 0, W, H);
    makeRoundRect(ctx, 14, 10, W - 28, H - 20, 22);
    // 行背景渐变。
    var rowGrad = ctx.createLinearGradient(0, 0, W, H);
    // 行背景透明度来自歌单架设置。
    var rowBgAlpha = shelfSettings().bgOpacity;
    // 中心行背景至少保持较高不透明度。
    var centerRowBgAlpha = isCenter ? Math.max(rowBgAlpha, 0.92) : rowBgAlpha;
    if (isCenter) {
      // 中心行使用更亮的层次。
      rowGrad.addColorStop(0, 'rgba(8,14,24,' + Math.min(0.985, centerRowBgAlpha + 0.040).toFixed(3) + ')');
      rowGrad.addColorStop(0.48, 'rgba(0,0,0,' + Math.min(0.985, centerRowBgAlpha + 0.030).toFixed(3) + ')');
      rowGrad.addColorStop(1, 'rgba(0,0,0,' + Math.min(0.98, centerRowBgAlpha + 0.015).toFixed(3) + ')');
    } else {
      // 普通行更低对比。
      rowGrad.addColorStop(0, 'rgba(16,16,20,' + Math.max(0.20, rowBgAlpha - 0.02).toFixed(3) + ')');
      rowGrad.addColorStop(1, 'rgba(0,0,0,' + Math.max(0.20, rowBgAlpha - 0.04).toFixed(3) + ')');
    }
    if (isCenter) {
      // 中心行给轻微强调色阴影。
      ctx.shadowColor = canvasAccent(0.20);
      ctx.shadowBlur = 18;
    }
    ctx.fillStyle = rowGrad;
    ctx.fill();
    ctx.shadowBlur = 0;
    ctx.strokeStyle = isCenter ? canvasAccent(0.48) : 'rgba(255,255,255,0.10)';
    ctx.lineWidth = isCenter ? 1.6 : 1;
    ctx.stroke();
    ctx.font = '700 18px Inter, Arial';
    ctx.fillStyle = isCenter ? canvasAccent(0.95) : 'rgba(255,255,255,0.34)';
    // 行号文本。
    var n = String(row.index + 1);
    if (n.length < 2) n = '0' + n;
    ctx.fillText(n, 32, 52);
    // 歌曲封面尺寸。
    var coverSize = 54;
    // 歌曲封面 X 坐标。
    var coverX = 84;
    // 歌曲封面 Y 坐标。
    var coverY = H/2 - coverSize/2;
    // 歌曲封面地址。
    var songCover = songCoverSrc(song, 80);
    // 是否存在歌曲封面。
    var hasSongCover = !!songCover;
    if (actionReady || hasSongCover) {
      // 行封面底板。
      makeRoundRect(ctx, coverX, coverY, coverSize, coverSize, 13);
      ctx.fillStyle = isCenter ? canvasAccent(0.12) : 'rgba(255,255,255,0.07)';
      ctx.fill();
      if (hasSongCover) {
        // 歌曲封面缓存。
        var songCoverRec = playlistCoverCache[songCover];
        if (songCoverRec && songCoverRec.loaded && songCoverRec.img) {
          // 封面已加载时裁剪绘制。
          ctx.save();
          makeRoundRect(ctx, coverX, coverY, coverSize, coverSize, 13);
          ctx.clip();
          ctx.drawImage(songCoverRec.img, coverX, coverY, coverSize, coverSize);
          ctx.restore();
        } else if (!songCoverRec || (!songCoverRec.loading && !songCoverRec.failed)) {
          // 封面未加载时请求并在完成后重绘当前行。
          requestPlaylistCover(songCover, function(){
            if (row && row.mesh && row.mesh.parent) drawRow(row, row.song, !!row.lastCenter);
          });
        }
      }
    }
    // 标题
    // 文本起始 X 会根据是否有封面调整。
    var textX = (actionReady || hasSongCover) ? 154 : 82;
    // 播放按钮尺寸和位置。
    var btnW = 104, btnH = 48, btnX = W - 144, btnY = H/2 - btnH/2;
    // 下一首按钮尺寸和位置。
    var miniBtn = 44, nextX = btnX - 52;
    // 文本最大宽度，中心行需要给按钮预留空间。
    var textMax = actionReady && isCenter ? nextX - textX - 24 : W - textX - 42;
    // 当前行是否为加载骨架行。
    var loadingRow = !playable && isLoadingLabel(song && song.name);
    if (loadingRow) {
      // 加载骨架标题。
      ctx.font = '700 22px Inter, "Microsoft YaHei", Arial';
      ctx.fillStyle = 'rgba(255,247,224,0.88)';
      ctx.fillText('正在更新队列', textX, 42);
      // 骨架扫光相位。
      var phase = ((uniforms.uTime.value || 0) * 0.85) % 1;
      for (var sk = 0; sk < 3; sk++) {
        // 骨架条 Y 坐标。
        var barY = 58 + sk * 13;
        // 骨架条宽度。
        var barW = sk === 0 ? 330 : (sk === 1 ? 250 : 180);
        makeRoundRect(ctx, textX, barY, barW, 7, 4);
        // 骨架条扫光渐变。
        var skGrad = ctx.createLinearGradient(textX, barY, textX + barW, barY);
        // 当前骨架条高光位置。
        var hot = (phase + sk * 0.14) % 1;
        skGrad.addColorStop(0, 'rgba(255,255,255,0.08)');
        skGrad.addColorStop(Math.max(0, hot - 0.18), canvasAccent(0.10));
        skGrad.addColorStop(Math.min(0.99, hot), canvasAccent(0.34));
        skGrad.addColorStop(1, 'rgba(255,255,255,0.08)');
        ctx.fillStyle = skGrad; ctx.fill();
      }
      // 加载行纹理需要随动画刷新。
      row.texture.needsUpdate = true;
      return;
    }
    // 歌曲标题。
    ctx.font = isCenter ? '800 24px Inter, "Microsoft YaHei", Arial' : '600 20px Inter, "Microsoft YaHei", Arial';
    ctx.fillStyle = isCenter ? 'rgba(255,247,224,0.96)' : 'rgba(255,255,255,0.80)';
    ctx.fillText(ellipsize(ctx, song.name || '', textMax), textX, 44);
    // 歌手文本。
    ctx.font = '500 15px Inter, "Microsoft YaHei", Arial';
    ctx.fillStyle = isCenter ? 'rgba(255,255,255,0.88)' : 'rgba(255,255,255,0.64)';
    ctx.fillText(ellipsize(ctx, song.artist || '', textMax), textX, 72);
    // center 行右侧显示下一首/播放按钮
    if (isCenter && actionReady) {
      // 下一首按钮底板。
      makeRoundRect(ctx, nextX, btnY + 2, miniBtn, btnH - 4, 15);
      // 下一首按钮渐变。
      var nextGrad = ctx.createLinearGradient(nextX, btnY + 2, nextX + miniBtn, btnY + btnH);
      nextGrad.addColorStop(0, 'rgba(255,255,255,0.082)');
      nextGrad.addColorStop(0.62, 'rgba(255,255,255,0.045)');
      nextGrad.addColorStop(1, canvasAccent(0.055));
      ctx.fillStyle = nextGrad;
      ctx.fill();
      ctx.strokeStyle = canvasAccent(0.24);
      ctx.lineWidth = 1.1;
      ctx.stroke();
      // 下一首按钮中心点。
      var nextCx = nextX + miniBtn / 2;
      // 下一首按钮中心 Y。
      var nextCy = btnY + btnH / 2;
      ctx.strokeStyle = 'rgba(255,255,255,0.90)';
      ctx.lineWidth = 2.8;
      ctx.lineCap = 'round';
      ctx.beginPath();
      ctx.moveTo(nextCx, nextCy - 8);
      ctx.lineTo(nextCx, nextCy + 8);
      ctx.moveTo(nextCx - 8, nextCy);
      ctx.lineTo(nextCx + 8, nextCy);
      ctx.stroke();

      // 播放按钮底板。
      makeRoundRect(ctx, btnX, btnY, btnW, btnH, 18);
      // 播放按钮渐变。
      var btnGrad = ctx.createLinearGradient(btnX, btnY, btnX + btnW, btnY + btnH);
      btnGrad.addColorStop(0, 'rgba(255,255,255,0.88)');
      btnGrad.addColorStop(0.56, canvasAccent(0.94));
      btnGrad.addColorStop(1, canvasAccent(0.58));
      ctx.fillStyle = btnGrad; ctx.fill();
      ctx.strokeStyle = canvasAccent(0.42);
      ctx.lineWidth = 1.2;
      ctx.stroke();
      ctx.font = '700 15px Inter, Arial';
      ctx.fillStyle = readableInkForHex(shelfAccentHex());
      ctx.fillText('播放', btnX + 36, btnY + 29);
    }
    // 标记行纹理需要上传。
    row.texture.needsUpdate = true;
  }

  // 按当前中心索引摆放二级内容中的一行。
  function place(row, i) {
    // 与中心行的距离。
    var delta = row.index - centerSmooth;
    // 距离绝对值。
    var absD = Math.abs(delta);
    if (absD > CONTENT_VISIBLE_RADIUS + 0.5) { row.mesh.visible = false; return; }
    row.mesh.visible = true;
    // 中心附近行层级更高。
    row.mesh.renderOrder = 240 + Math.round((CONTENT_VISIBLE_RADIUS + 1 - Math.min(absD, CONTENT_VISIBLE_RADIUS + 1)) * 14);
    // 当前时间。
    var nowT = uniforms.uTime.value;
    // 行入场原始进度。
    var revealRaw = Math.max(0, Math.min(1, (nowT - rowAnimAt - absD * 0.040) / 0.72));
    // 行入场平滑进度。
    var reveal = revealRaw * revealRaw * (3 - 2 * revealRaw);
    // 指针视差 X。
    var parX = pointerParallax.x || 0;
    // 指针视差 Y。
    var parY = pointerParallax.y || 0;
    // 离中心越远，指针影响越弱。
    var parWeight = Math.max(0, 1 - absD * 0.12);
    // 行点击脉冲。
    var pulse = row.fxPulse || 0;
    // 列表整体加载完成后的收敛动画。
    var settle = group && group.userData ? (group.userData.rowSettle || 0) : 0;
    // 当前详情布局。
    var layout = detailLayout();
    // 当前歌单架视觉设置。
    var shelfLook = shelfSettings();
    // 骷髅预设下详情面板使用更保守布局。
    var skullDetail = shouldUseSkullSafeShelfCamera();
    // 行基础 X。
    var rowBaseX = skullDetail ? 0.22 : -0.04;
    // 行随距离展开的 X 偏移。
    var rowSpreadX = skullDetail ? 0.030 : 0.014;
    // 行入场 X 偏移。
    var rowIntroX = skullDetail ? 0.58 : 0.38;
    // 中心行 Z。
    var rowCenterZ = skullDetail ? 0.62 : 0.62;
    // 非中心行基础 Z。
    var rowBackZ = skullDetail ? 0.58 : 0.58;
    // 行深度步进。
    var rowDepthStep = skullDetail ? 0.046 : 0.048;
    // 行最终 X。
    var px = rowBaseX + absD * rowSpreadX + (1 - reveal) * (rowIntroX + absD * rowSpreadX);
    // 行最终 Y。
    var py = -delta * layout.rowStep + (1 - reveal) * (0.20 + (delta < 0 ? -0.10 : 0.10));
    // 行最终 Z。
    var pz = (absD < 0.5 ? rowCenterZ : (rowBackZ - absD * rowDepthStep)) - (1 - reveal) * (skullDetail ? 0.10 : 0.16);
    // 叠加载入完成后的收敛偏移。
    px += settle * ((skullDetail ? 0.11 : 0.12) + absD * (skullDetail ? 0.010 : 0.012));
    py += settle * (delta < 0 ? -0.08 : 0.08);
    pz -= settle * (skullDetail ? 0.045 : 0.08);
    // 叠加指针视差。
    px += parX * (skullDetail ? 0.022 : 0.026) * parWeight;
    py += parY * (skullDetail ? 0.024 : 0.036) * parWeight;
    pz += (parY * (skullDetail ? 0.014 : 0.024) - parX * (skullDetail ? 0.010 : 0.020)) * parWeight;
    // 行缩放。
    var scale = (absD < 0.5 ? 1.00 : Math.max(0.66, 0.94 - absD * 0.070)) * (0.90 + reveal * 0.10) * (1 + pulse * 0.052) * (1 - settle * 0.025) * layout.rowScale;
    row.mesh.position.set(px, py, pz);
    row.mesh.scale.setScalar(scale);
    // 行基础透明度。
    var rowOpacityBase = Math.min(1, (absD < 0.5 ? 1.0 : Math.max(0.34, 1.0 - absD * 0.12)) * reveal + pulse * 0.14);
    // 中心行保持更高不透明度。
    var rowOpacityScale = absD < 0.5 ? Math.max(0.94, shelfLook.opacity) : shelfLook.opacity;
    row.mesh.material.opacity = Math.min(1, rowOpacityBase * rowOpacityScale);
    row.mesh.rotation.y = (skullDetail ? -0.070 : 0.10) + (1 - reveal) * (skullDetail ? 0.018 : 0.052) + parX * (skullDetail ? 0.010 : 0.018) * parWeight;
    row.mesh.rotation.x = (skullDetail ? 0.010 : 0) - delta * (skullDetail ? 0.010 : 0.022) - parY * (skullDetail ? 0.006 : 0.014) * parWeight;
  }

  // 释放一组二级内容行资源。
  function disposeRowList(rowList) {
    while (rowList.length) {
      // 取出一行。
      var row = rowList.pop();
      // 从场景中移除行 mesh。
      if (row.mesh && row.mesh.parent) row.mesh.parent.remove(row.mesh);
      if (row.mesh && row.mesh.material) {
        // 释放行贴图。
        if (row.mesh.material.map) row.mesh.material.map.dispose();
        // 释放行材质。
        row.mesh.material.dispose();
      }
      // 释放行几何。
      if (row.mesh && row.mesh.geometry) row.mesh.geometry.dispose();
    }
  }

  // 释放当前二级内容行窗口。
  function disposeRows() {
    disposeRowList(rows);
    renderedStart = -1;
  }

  // 释放被动画捕获的旧详情组、旧行和旧面板。
  function disposeCapturedDetail(targetGroup, targetRows, targetPanel) {
    if (targetGroup && targetGroup.parent) targetGroup.parent.remove(targetGroup);
    disposeRowList(targetRows || []);
    disposePanelObject(targetPanel);
  }

  // 二级内容行加载完成后启动一次收敛入场动画。
  function startRowsLoadedIntro() {
    // 重置行动画时间。
    rowAnimAt = uniforms.uTime.value;
    // 标记面板和行需要重绘。
    panelDirty = true;
    rowsDirty = true;
    if (!group || !group.userData) return;
    // rowSettle 从 1 缓动到 0。
    group.userData.rowSettle = 1;
    if (window.gsap) {
      window.gsap.killTweensOf(group.userData, 'rowSettle');
      window.gsap.to(group.userData, { rowSettle: 0, duration: 0.76, ease: 'expo.out' });
    } else {
      group.userData.rowSettle = 0;
    }
  }

  // 同步二级内容当前中心附近的行渲染窗口。
  function syncRenderedRows(force) {
    if (!group) return;
    // 当前视觉时间。
    var nowT = uniforms.uTime.value || 0;
    // 加载占位需要按固定间隔刷新骨架动画。
    var refreshLoading = isLoadingContent() && nowT - rowDrawAt >= LOADING_ANIM_INTERVAL;
    drawPanelIfNeeded(force || refreshLoading, nowT);
    // 全量歌曲行数。
    var total = allTracks.length;
    if (!total) { disposeRows(); return; }
    // 当前中心索引。
    var center = Math.round(centerTarget);
    // 行窗口起点。
    var start = Math.max(0, center - CONTENT_VISIBLE_RADIUS);
    // 行窗口终点。
    var end = Math.min(total - 1, start + CONTENT_MAX_RENDER - 1);
    // 靠近末尾时回推起点，让窗口尽量填满。
    start = Math.max(0, end - CONTENT_MAX_RENDER + 1);
    if (!force && start === renderedStart && rows.length === (end - start + 1)) {
      // 窗口未变时同步行数据引用。
      rows.forEach(function(row) { row.song = allTracks[row.index] || row.song; });
      if (rowsDirty || refreshLoading) {
        // 行脏或加载动画刷新时重绘当前窗口行。
        rows.forEach(function(row) {
          // 当前行是否为中心行。
          var isCenter = Math.abs(row.index - centerSmooth) < 0.5;
          drawRow(row, row.song, isCenter);
          row.lastCenter = isCenter;
        });
        rowsDirty = false;
        rowDrawAt = nowT;
      }
      return;
    }
    // 窗口变化时销毁旧行。
    disposeRows();
    // 保存新窗口起点。
    renderedStart = start;
    for (var idx = start; idx <= end; idx++) {
      // 创建并绘制窗口内每一行。
      var row = makeRow(allTracks[idx], idx);
      rows.push(row);
      drawRow(row, row.song, idx === Math.round(centerSmooth));
      row.lastCenter = idx === Math.round(centerSmooth);
    }
    rowsDirty = false;
    rowDrawAt = nowT;
  }

  // 暴露二级内容列表管理器接口。
  return {
    // 二级内容是否打开。
    isOpen: function() { return open; },
    // 主题变化后强制重绘面板和行。
    refreshTheme: function() {
      panelDirty = true;
      rowsDirty = true;
      if (!open || !group) return;
      drawPanelIfNeeded(true);
      syncRenderedRows(true);
    },
    // 打开二级内容列表。
    open: async function(playlistId, title, fromCard) {
      // 标记打开状态并记录标题和来源卡片。
      open = true;
      playlistTitle = title;
      sourceCard = fromCard;
      // 请求 token 防止旧异步流程回写。
      var token = ++requestToken;
      // 打开和行动画时间。
      openAnimAt = uniforms.uTime.value;
      rowAnimAt = openAnimAt;
      // 打开时从第一行开始。
      centerTarget = 0;
      centerSmooth = 0;
      // 标记所有画布需要重绘。
      panelDirty = true;
      rowsDirty = true;
      panelDrawAt = -10;
      rowDrawAt = -10;
      if (!group) {
        // 首次打开时创建详情根组。
        group = new THREE.Group();
        scene.add(group);
      }
      // 打开时的响应式布局。
      var openLayout = detailLayout();
      // 骷髅预设详情安全姿态。
      var openSkullDetail = shouldUseSkullSafeShelfCamera();
      // 非骷髅预设可根据相机动态姿态打开。
      var openDynamicDetail = !openSkullDetail && shouldUseShelfDynamicCamera('shelf-detail') && camera;
      // 当前封面粒子旋转，普通姿态会继承一部分。
      var openCoverRx = particles && particles.rotation ? particles.rotation.x : 0;
      var openCoverRy = particles && particles.rotation ? particles.rotation.y : 0;
      var openCoverRz = particles && particles.rotation ? particles.rotation.z : 0;
      // detailIntro 控制打开入场偏移。
      group.userData.detailIntro = 1;
      group.position.set(openLayout.x + (openSkullDetail ? 0.10 : 0.16), openLayout.y - (openSkullDetail ? 0.02 : 0.024), openLayout.z - (openSkullDetail ? 0.05 : 0.070));
      if ((openSkullDetail || openDynamicDetail) && camera) {
        // 安全或动态姿态使用相机朝向作为基准。
        group.quaternion.copy(camera.quaternion);
        group.rotateX(openLayout.rx);
        group.rotateY(openLayout.ry + (openSkullDetail ? 0.014 : 0.018));
      } else {
        // 普通姿态继承封面粒子部分旋转。
        group.rotation.y = openCoverRy * 0.82 + openLayout.ry + 0.018;
        group.rotation.x = openCoverRx * 0.72 + openLayout.rx;
        group.rotation.z = openCoverRz * 0.70;
      }
      group.scale.setScalar(openLayout.scale * 0.965);
      if (window.gsap) {
        // 使用 GSAP 平滑收敛入场偏移。
        window.gsap.killTweensOf(group.userData);
        window.gsap.to(group.userData, { detailIntro: 0, duration: 0.48, ease: 'power3.out' });
      } else {
        group.userData.detailIntro = 0;
      }
      try {
        // 先绘制面板和加载行，让打开动作有即时反馈。
        drawPanelIfNeeded(true);
        // 清旧
        disposeRows();
        // loading 行
        // 加载占位行。
        allTracks = [{ name: '加载中…', artist: '' }];
        panelDirty = true;
        rowsDirty = true;
        syncRenderedRows(true);
      } catch (renderLoadingErr) {
        console.warn('[ShelfContentLoadingRender]', playlistId, renderLoadingErr);
      }
      if (!open || token !== requestToken) return;
      try {
        // 在线歌单入口已移除，仅保留宿主队列展示。
        disposeRows();
        // 用固定文案替代旧在线歌单内容。
        allTracks = [{ name: '在线歌单已移除', artist: '播放队列由宿主同步' }];
        centerTarget = 0; centerSmooth = 0;
        panelDirty = true;
        rowsDirty = true;
        startRowsLoadedIntro();
        syncRenderedRows(true);
      } catch (renderReadyErr) {
        console.warn('[ShelfContentReadyRender]', playlistId, renderReadyErr);
        showToast('在线歌单已移除');
      }
    },
    close: function() {
      open = false;
      requestToken++;
      var targetGroup = group;
      var targetRows = rows.slice();
      var targetPanel = panel;
      group = null;
      rows = [];
      panel = null;
      renderedStart = -1;
      allTracks = [];
      sourceCard = null;
      panelDirty = true;
      rowsDirty = true;
      panelDrawAt = -10;
      rowDrawAt = -10;
      if (!targetGroup) return;
      var materials = targetRows.map(function(row){ return row.mesh && row.mesh.material; }).filter(Boolean);
      if (targetPanel && targetPanel.mesh && targetPanel.mesh.material) materials.push(targetPanel.mesh.material);
      if (window.gsap) {
        window.gsap.killTweensOf(targetGroup.position);
        window.gsap.killTweensOf(targetGroup.scale);
        window.gsap.to(targetGroup.scale, { x: 0.965, y: 0.965, z: 0.965, duration: 0.18, ease: 'power2.in' });
        window.gsap.to(targetGroup.position, {
          x: targetGroup.position.x + 0.18,
          y: targetGroup.position.y - 0.02,
          z: targetGroup.position.z - 0.10,
          duration: 0.18,
          ease: 'power2.in'
        });
        var finishClose = function(){ disposeCapturedDetail(targetGroup, targetRows, targetPanel); };
        if (materials.length) {
          window.gsap.to(materials, {
            opacity: 0,
            duration: 0.16,
            ease: 'power2.in',
            onComplete: finishClose
          });
        } else {
          window.gsap.delayedCall(0.18, finishClose);
        }
      } else {
        disposeCapturedDetail(targetGroup, targetRows, targetPanel);
      }
    },
    update: function(dt) {
      if (!group || !open) return;
      var intro = group.userData.detailIntro || 0;
      var parX = pointerParallax.x || 0;
      var parY = pointerParallax.y || 0;
      var layout = detailLayout();
      var skullDetail = shouldUseSkullSafeShelfCamera();
      var dynamicDetail = !skullDetail && shouldUseShelfDynamicCamera('shelf-detail') && camera;
      var coverBoundDetail = !skullDetail && !dynamicDetail && particles && particles.rotation;
      var coverBindX = coverBoundDetail ? particles.rotation.y * 0.18 : 0;
      var coverBindY = coverBoundDetail ? particles.rotation.x * -0.16 : 0;
      var coverBindZ = coverBoundDetail ? Math.abs(particles.rotation.y) * 0.030 : 0;
      group.position.set(
        layout.x + coverBindX + intro * (skullDetail ? 0.10 : 0.16) + parX * (skullDetail ? 0.024 : 0.030),
        layout.y + coverBindY - intro * (skullDetail ? 0.02 : 0.024) + parY * (skullDetail ? 0.026 : 0.026),
        layout.z + coverBindZ - intro * (skullDetail ? 0.05 : 0.070) + parY * (skullDetail ? 0.014 : 0.016) - parX * (skullDetail ? 0.010 : 0.010)
      );
      if (skullDetail && camera) {
        group.quaternion.copy(camera.quaternion);
        group.rotateX(layout.rx - parY * 0.004);
        group.rotateY(layout.ry + intro * 0.004 + parX * 0.004);
      } else if (dynamicDetail) {
        group.quaternion.copy(camera.quaternion);
        group.rotateX(layout.rx - parY * 0.006);
        group.rotateY(layout.ry + intro * 0.012 + parX * 0.008);
      } else {
        var coverRx = particles && particles.rotation ? particles.rotation.x : 0;
        var coverRy = particles && particles.rotation ? particles.rotation.y : 0;
        var coverRz = particles && particles.rotation ? particles.rotation.z : 0;
        group.rotation.x += ((coverRx * 0.72 + layout.rx - parY * 0.010) - group.rotation.x) * 0.16;
        group.rotation.y += ((coverRy * 0.82 + layout.ry + intro * 0.018 + parX * 0.014) - group.rotation.y) * 0.16;
        group.rotation.z += ((coverRz * 0.70) - group.rotation.z) * 0.14;
      }
      group.scale.setScalar(layout.scale * (1 - intro * (skullDetail ? 0.020 : 0.035)));
      centerSmooth += (centerTarget - centerSmooth) * 0.18;
      if (Math.abs(centerSmooth - centerTarget) < 0.001) centerSmooth = centerTarget;
      syncRenderedRows(false);
      if (panel && panel.mesh) {
        var pr = Math.max(0, Math.min(1, (uniforms.uTime.value - openAnimAt) / 0.72));
        pr = pr * pr * (3 - 2 * pr);
        panel.mesh.material.opacity = 0.86 * pr * shelfSettings().opacity;
      }
      for (var i = 0; i < rows.length; i++) {
        place(rows[i], i);
        var isC = Math.abs(rows[i].index - centerSmooth) < 0.5;
        if (rows[i].lastCenter !== isC) {
          rows[i].lastCenter = isC;
          drawRow(rows[i], rows[i].song, isC);
        }
      }
    },
    next: function() {
      if (allTracks.length) {
        var prevTarget = Math.round(centerTarget);
        centerTarget = Math.min(allTracks.length - 1, centerTarget + 1);
        var nextTarget = Math.round(centerTarget);
        syncRenderedRows(false);
        if (nextTarget !== prevTarget) playShelfSelectTick(1, 'row');
        pulseObjectValue(rows.find(function(r){ return r.index === nextTarget; }), 'fxPulse', 0.48, 0.36);
      }
    },
    // 二级内容向上一行移动。
    prev: function() {
      if (allTracks.length) {
        // 移动前中心索引。
        var prevTarget = Math.round(centerTarget);
        // 目标索引向前夹紧。
        centerTarget = Math.max(0, centerTarget - 1);
        // 移动后中心索引。
        var nextTarget = Math.round(centerTarget);
        syncRenderedRows(false);
        if (nextTarget !== prevTarget) playShelfSelectTick(-1, 'row');
        pulseObjectValue(rows.find(function(r){ return r.index === nextTarget; }), 'fxPulse', 0.48, 0.36);
      }
    },
    // 二级内容按给定步长滚动。
    scrollBy: function(d) {
      if (allTracks.length) {
        // 滚动前中心索引。
        var prevTarget = Math.round(centerTarget);
        // 滚动后目标中心索引。
        centerTarget = Math.max(0, Math.min(allTracks.length - 1, centerTarget + d));
        // 归一化后的目标中心索引。
        var nextTarget = Math.round(centerTarget);
        syncRenderedRows(false);
        if (nextTarget !== prevTarget) playShelfSelectTick(d, 'row');
        pulseObjectValue(rows.find(function(r){ return r.index === nextTarget; }), 'fxPulse', 0.48, 0.36);
      }
    },
    // 获取当前已渲染行。
    getRows: function() { return rows; },
    // 获取当前中心行索引。
    getCenterIdx: function() { return Math.round(centerSmooth); },
    // 给指定行施加脉冲反馈。
    pulseRow: function(row, amount) {
      if (!row) return;
      pulseObjectValue(row, 'fxPulse', amount || 1, 0.42);
    },
    // 使用 Three.js 射线拾取二级内容行。
    raycastRows: function(rc) {
      if (!rows.length) return null;
      // 可见行 mesh 列表。
      var vm = rows.filter(function(r){return r.mesh.visible;}).map(function(r){return r.mesh;});
      // 射线命中结果。
      var hits = rc.intersectObjects(vm, false);
      if (!hits.length) return null;
      // 命中的行对象。
      var row = rows.find(function(r){ return r.mesh === hits[0].object; });
      return { row: row, uv: hits[0].uv };
    },
    // 用屏幕坐标粗略拾取二级内容行。
    pickRowAtScreen: function(sx, sy) {
      if (!rows.length || !open) return null;
      // 按层级从前到后检查。
      var ordered = rows.filter(function(r){ return r.mesh && r.mesh.visible; }).sort(function(a, b){
        return (b.mesh.renderOrder || 0) - (a.mesh.renderOrder || 0);
      });
      for (var ri = 0; ri < ordered.length; ri++) {
        // 当前候选行。
        var row = ordered[ri];
        // 行几何尺寸。
        var params = row.mesh.geometry && row.mesh.geometry.parameters || {};
        // 半宽。
        var hw = (params.width || 2.50) / 2;
        // 半高。
        var hh = (params.height || 0.36) / 2;
        // 行四角本地坐标。
        var pts = [
          new THREE.Vector3(-hw, -hh, 0),
          new THREE.Vector3( hw, -hh, 0),
          new THREE.Vector3( hw,  hh, 0),
          new THREE.Vector3(-hw,  hh, 0),
        ];
        // 屏幕包围盒。
        var minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
        row.mesh.updateMatrixWorld(true);
        for (var pi = 0; pi < pts.length; pi++) {
          // 投影到屏幕坐标。
          pts[pi].applyMatrix4(row.mesh.matrixWorld).project(camera);
          var x = (pts[pi].x + 1) * innerWidth / 2;
          var y = (1 - pts[pi].y) * innerHeight / 2;
          minX = Math.min(minX, x); maxX = Math.max(maxX, x);
          minY = Math.min(minY, y); maxY = Math.max(maxY, y);
        }
        // 命中扩展边距。
        var padX = 24, padY = 16;
        if (sx < minX - padX || sx > maxX + padX || sy < minY - padY || sy > maxY + padY) continue;
        // 近似 UV。
        var u = clampRange((sx - minX) / Math.max(1, maxX - minX), 0, 1);
        var v = 1 - clampRange((sy - minY) / Math.max(1, maxY - minY), 0, 1);
        return { row: row, uv: { x: u, y: v }, screenPick: true };
      }
      return null;
    },
    // 射线拾取二级内容背景面板。
    raycastPanel: function(rc) {
      if (!panel || !panel.mesh) return null;
      var hits = rc.intersectObject(panel.mesh, false);
      return hits && hits.length ? hits[0] : null;
    },
    // 判断屏幕坐标是否落在二级内容面板投影范围内。
    screenContainsPanel: function(sx, sy) {
      if (!panel || !panel.mesh || !open) return false;
      // 面板几何尺寸。
      var params = panel.mesh.geometry && panel.mesh.geometry.parameters || {};
      // 半宽。
      var hw = (params.width || 2.62) / 2;
      // 半高。
      var hh = (params.height || 3.02) / 2;
      // 面板四角本地坐标。
      var pts = [
        new THREE.Vector3(-hw, -hh, 0),
        new THREE.Vector3( hw, -hh, 0),
        new THREE.Vector3( hw,  hh, 0),
        new THREE.Vector3(-hw,  hh, 0),
      ];
      // 面板屏幕包围盒。
      var minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
      panel.mesh.updateMatrixWorld(true);
      for (var pi = 0; pi < pts.length; pi++) {
        // 投影到屏幕坐标。
        pts[pi].applyMatrix4(panel.mesh.matrixWorld).project(camera);
        var x = (pts[pi].x + 1) * innerWidth / 2;
        var y = (1 - pts[pi].y) * innerHeight / 2;
        minX = Math.min(minX, x); maxX = Math.max(maxX, x);
        minY = Math.min(minY, y); maxY = Math.max(maxY, y);
      }
      // 面板命中边距。
      var pad = 42;
      return sx >= minX - pad && sx <= maxX + pad && sy >= minY - pad && sy <= maxY + pad;
    },
    // 判断点击中心行右侧按钮区域对应的动作。
    rowActionAtScreen: function(row, sx, sy) {
      if (!row || !row.mesh || !row.mesh.visible) return null;
      // 行歌曲数据。
      var song = row.song || {};
      // 只有中心行有按钮动作。
      var isCenter = Math.abs(row.index - Math.round(centerSmooth)) < 0.5;
      if (!isCenter || !(song && song.id)) return null;
      // 行几何尺寸。
      var params = row.mesh.geometry && row.mesh.geometry.parameters || {};
      // 半宽。
      var hw = (params.width || 2.50) / 2;
      // 半高。
      var hh = (params.height || 0.36) / 2;
      // 行四角坐标。
      var corners = [
        new THREE.Vector3(-hw, -hh, 0),
        new THREE.Vector3( hw, -hh, 0),
        new THREE.Vector3( hw,  hh, 0),
        new THREE.Vector3(-hw,  hh, 0),
      ];
      // 投影包围盒。
      var minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
      row.mesh.updateMatrixWorld(true);
      for (var i = 0; i < corners.length; i++) {
        // 投影到屏幕坐标。
        corners[i].applyMatrix4(row.mesh.matrixWorld).project(camera);
        var x = (corners[i].x + 1) * innerWidth / 2;
        var y = (1 - corners[i].y) * innerHeight / 2;
        minX = Math.min(minX, x); maxX = Math.max(maxX, x);
        minY = Math.min(minY, y); maxY = Math.max(maxY, y);
      }
      // 包围盒宽度。
      var w = Math.max(1, maxX - minX);
      // 包围盒高度。
      var h = Math.max(1, maxY - minY);
      // 点击点在行内的归一化 X。
      var u = clampRange((sx - minX) / w, 0, 1);
      // 点击点在行内的归一化 Y。
      var v = clampRange((sy - minY) / h, 0, 1);
      if (u >= 0.75 && u < 0.82 && v > 0.12 && v < 0.88) return 'next';
      if (u >= 0.82 && v > 0.10 && v < 0.90) return 'play';
      return null;
    },
    // 播放二级内容中的歌曲行。
    playRow: function(row) {
      // 旧在线歌单播放入口已移除。
      pulseObjectValue(row, 'fxPulse', 1.0, 0.34);
      // 行索引。
      var idx = row.index;
      if (idx < 0) return;
      // 只有真实歌曲才可播放。
      var songToPlay = row.song && row.song.id ? row.song : null;
      if (!songToPlay) return;
      forcePlaybackControlsInteractive();
      requestHostPlaySong(songToPlay);
      // 关闭内容框
      // 播放后关闭二级内容框。
      var sm = shelfManager;
      if (sm) safeShelfCloseContent('content-play-row');
    }
  };

  // 构建二级内容中的一行 3D 网格。
  function makeRow(song, i) {
    // 行 canvas。
    var cv = document.createElement('canvas');
    cv.width = 800; cv.height = 104;
    // 行绘制上下文。
    var ctx = cv.getContext('2d');
    // 行 canvas 纹理。
    var tx = new THREE.CanvasTexture(cv);
    tx.minFilter = THREE.LinearFilter; tx.magFilter = THREE.LinearFilter;
    tx.generateMipmaps = false;
    // 行材质。
    var mat = new THREE.MeshBasicMaterial({ map: tx, transparent: true, opacity: 0.96, depthWrite: false, depthTest: false, side: THREE.DoubleSide });
    // 行几何体。
    var geo = new THREE.PlaneGeometry(2.50, 0.36, 1, 1);
      // 行 mesh。
      var mesh = new THREE.Mesh(geo, mat);
    mesh.renderOrder = 240 + i;
      group.add(mesh);
      // 行运行期对象。
      return { canvas: cv, texture: tx, mesh: mesh, song: song, index: i, fxPulse: 0 };
    }
}

// 将大数字压缩成中文单位显示。
function compactCount(n) {
  n = Number(n) || 0;
  if (n >= 100000000) return (n / 100000000).toFixed(1) + '亿';
  if (n >= 10000) return (n / 10000).toFixed(1) + '万';
  return String(n);
}
// 请求并缓存播放列表或歌曲封面图片。
function requestPlaylistCover(url, cb) {
  if (!url) { if (cb) cb(null); return; }
  // 当前 URL 的缓存记录。
  var rec = playlistCoverCache[url];
  if (rec && rec.loaded) { if (cb) setTimeout(function(){ cb(rec.img); }, 0); return; }
  if (rec && rec.loading) { if (cb) rec.waiters.push(cb); return; }
  // 创建新的加载记录。
  rec = playlistCoverCache[url] = { loaded:false, loading:true, waiters: cb ? [cb] : [], img:null, failed:false };

  // 封面加载成功收尾。
  function finish(img) {
    rec.loaded = true; rec.loading = false; rec.failed = false; rec.img = img;
    rec.waiters.splice(0).forEach(function(fn){ setTimeout(function(){ fn(img); }, 0); });
  }
  // 封面加载失败收尾。
  function fail() {
    rec.loading = false; rec.failed = true;
    rec.waiters.splice(0).forEach(function(fn){ setTimeout(function(){ fn(null); }, 0); });
  }
  // 按候选地址顺序尝试加载封面。
  function loadCandidate(srcList, index) {
    // 当前候选地址。
    var src = srcList[index];
    if (!src) { fail(); return; }
    // 图片对象。
    var img = new Image();
    if (!isInlineCoverSrc(src)) img.crossOrigin = 'anonymous';
    img.onload = function(){ finish(img); };
    img.onerror = function(){ loadCandidate(srcList, index + 1); };
    img.src = src;
  }

  // 优先尝试代理地址，避免 canvas 污染。
  var proxied = coverProxySrc(url);
  // 候选加载源列表。
  var sources = [];
  if (proxied) sources.push(proxied);
  if (url && sources.indexOf(url) === -1 && (isInlineCoverSrc(url) || isProxyableCoverUrl(url))) sources.push(url);
  loadCandidate(sources, 0);
}

// ============================================================
//  3D 卡片交互 - PSP 风格
//   - 滚轮: 滚动 center 卡 (一级或二级)
//   - 点击 center 卡: 播放队列
//   - 点击两侧卡: 滚到那张
//   - ESC: 关闭内容框
// ============================================================
// 根据指针事件创建 Three.js 射线。
function raycasterFromPointerEvent(e) {
  // 归一化设备坐标 X。
  var mx = (e.clientX / innerWidth) * 2 - 1;
  // 归一化设备坐标 Y。
  var my = -(e.clientY / innerHeight) * 2 + 1;
  // 射线对象。
  var rc = new THREE.Raycaster();
  rc.setFromCamera(new THREE.Vector2(mx, my), camera);
  return rc;
}
// 优先用射线拾取歌单架卡片，失败时回退到屏幕矩形拾取。
function pointerCardHit(rc, e, screenPad) {
  if (!shelfManager) return null;
  return shelfManager.raycastCards(rc) || (shelfManager.pickCardAtScreen && shelfManager.pickCardAtScreen(e.clientX, e.clientY, screenPad));
}
// 判断当前指针位置是否命中侧边歌单架焦点区。
function isSideShelfFocusHit(e) {
  if (!e || !shelfManager || !shelfManager.getMode || shelfManager.getMode() !== 'side') return false;
  if (shelfPinnedOpen) return true;
  if (shelfAlwaysVisible()) return !!pointerCardHit(raycasterFromPointerEvent(e), e, 18);
  if (!shelfAutoHiddenInputReady()) return false;
  if (shelfVisibility > 0.34 && (isShelfClickZone(e) || isShelfPreviewUseZone(e))) return true;
  return !!(shelfPreviewIsVisible() && pointerCardHit(raycasterFromPointerEvent(e), e, 24));
}
// 根据鼠标位置刷新歌单架卡片悬停选中态。
function updateShelfCardHoverSelection(e) {
  if (!shelfManager || !shelfManager.clearSelected || !shelfManager.setSelected) return;
  if (!e || isPointerOverUi(e)) {
    shelfManager.clearSelected();
    return;
  }
  // 当前歌单架模式。
  var mode = shelfManager.getMode && shelfManager.getMode();
  if (!mode || mode === 'off') {
    shelfManager.clearSelected();
    return;
  }
  if (shelfManager.hasOpenContent && shelfManager.hasOpenContent()) {
    shelfManager.clearSelected();
    return;
  }
  // 管理器是否允许交互。
  var canInteract = shelfManager.canInteract && shelfManager.canInteract();
  if (!canInteract) {
    shelfManager.clearSelected();
    return;
  }
  if (mode === 'side') {
    if (!shelfPinnedOpen && shelfAlwaysVisible()) {
      // 常显侧边模式下只在真实命中卡片时选中。
      var alwaysHit = pointerCardHit(raycasterFromPointerEvent(e), e, 18);
      if (alwaysHit && alwaysHit.card) shelfManager.setSelected(alwaysHit.card.index);
      else shelfManager.clearSelected();
      return;
    }
    // 自动隐藏侧栏必须先进入可交互状态。
    var sideUsable = shelfPinnedOpen || shelfAutoHiddenInputReady();
    if (!sideUsable) {
      shelfManager.clearSelected();
      return;
    }
  } else if (mode !== 'stage') {
    shelfManager.clearSelected();
    return;
  }
  // 最终命中的卡片。
  var hit = pointerCardHit(raycasterFromPointerEvent(e), e);
  if (hit && hit.card) shelfManager.setSelected(hit.card.index);
  else shelfManager.clearSelected();
}
// 判断是否命中旧在线歌单播放按钮；当前功能已移除。
function isShelfPlaylistPlayHit(hit) {
  return false;
}
// 歌单架主点击事件。
renderer.domElement.addEventListener('click', function(e){
  if (!shelfManager || shelfManager.getMode() === 'off') return;
  if (isPointerOverUi(e)) return;
  if (mouseDownAt.hadDrag) { mouseDownAt.hadDrag = false; return; }

  // 当前点击射线。
  var rc = raycasterFromPointerEvent(e);
  // 当前歌单架模式。
  var mode = shelfManager.getMode();
  // 当前是否可交互。
  var canInteract = shelfManager.canInteract && shelfManager.canInteract();

  // 优先二级内容框
  if (shelfManager.hasOpenContent()) {
    // 二级内容管理器。
    var cl = shelfManager.getContentList && shelfManager.getContentList();
    if (cl) {
      // 先拾取二级行。
      var rowHit = cl.raycastRows(rc);
      if (!rowHit && cl.pickRowAtScreen) rowHit = cl.pickRowAtScreen(e.clientX, e.clientY);
      if (rowHit) {
        if (cl.pulseRow) cl.pulseRow(rowHit.row, 0.72);
        // 是否点击了中心行。
        var selectedRow = Math.abs(rowHit.row.index - cl.getCenterIdx()) < 0.5;
        // 行是否可播放。
        var rowIsPlayable = !!(rowHit.row.song && rowHit.row.song.id);
        // 是否命中下一首按钮。
        var hitNextButton = rowHit.uv && rowHit.uv.x >= 0.75 && rowHit.uv.x < 0.82 && rowHit.uv.y > 0.20 && rowHit.uv.y < 0.82;
        // 是否命中播放按钮。
        var hitPlayButton = rowHit.uv && rowHit.uv.x >= 0.82 && rowHit.uv.y > 0.20 && rowHit.uv.y < 0.82;
        // 屏幕坐标回退动作识别。
        var screenAction = (!rowHit.uv && cl.rowActionAtScreen) ? cl.rowActionAtScreen(rowHit.row, e.clientX, e.clientY) : null;
        hitNextButton = hitNextButton || screenAction === 'next';
        hitPlayButton = hitPlayButton || screenAction === 'play';
        if (selectedRow && rowIsPlayable && hitNextButton) {
          queueDetailSongNext(rowHit.row.song);
        } else if (rowIsPlayable || (selectedRow && rowIsPlayable && hitPlayButton)) {
          cl.playRow(rowHit.row);
        } else {
          // 滚到这行
          cl.scrollBy(rowHit.row.index - cl.getCenterIdx());
        }
        return;
      }
      // 未点中行时，点击一级卡片区域视为返回一级。
      var returnHit = shelfManager.raycastCards(rc);
      safeShelfCloseContent('shelf-card-return');
      if (mode === 'side') setShelfPinnedOpen(true, true);
      if (returnHit && returnHit.card) {
        shelfManager.scrollBy(returnHit.card.index - shelfManager.getCenterIdx());
      }
      return;
    }
  }

  // 一级卡片
  // 一级卡片命中。
  var hit = pointerCardHit(rc, e, mode === 'side' && !shelfPinnedOpen && shelfAlwaysVisible() ? 18 : undefined);
  if (mode === 'side' && !shelfPinnedOpen && !canUseSideShelfWithoutPinnedOpen()) return;

  if (hit) {
    if (mode === 'side') setShelfPinnedOpen(true, true);
    // 命中卡片索引。
    var idx = hit.card.index;
    if (Math.abs(idx - shelfManager.getCenterIdx()) < 0.5) {
      if (isShelfPlaylistPlayHit(hit) && shelfManager.playPlaylistAt && shelfManager.playPlaylistAt(idx)) return;
      shelfManager.openContent(idx);
    } else {
      shelfManager.scrollBy(idx - shelfManager.getCenterIdx());
    }
  } else if (mode === 'side' && shelfPinnedOpen) {
    setShelfPinnedOpen(false, true);
  }
});

// 画布右键保持无动作，仅阻止默认菜单。
renderer.domElement.addEventListener('contextmenu', function(e){
  e.preventDefault();
  e.stopPropagation();
});

// 滚轮: 在真实卡片或右侧窄热区内滚卡片; 否则保留给封面粒子/视角
//   side 模式: 常驻不再用半屏预览区接管滚轮
//   stage 模式: 鼠标 y > 60% 屏幕高
//   shift + wheel: 强制滚卡片
// 最近一次滚轮是否由歌单架接管。
var wheelOverShelf = false;
// 歌单架滚轮事件，优先让二级内容和卡片滚动响应。
renderer.domElement.addEventListener('wheel', function(e){
  if (isPointerOverUi(e)) return;
  if (!shelfManager || shelfManager.getMode() === 'off') return;
  markRenderInteraction('shelf-wheel', 900);
  // 当前滚轮射线。
  var rc = raycasterFromPointerEvent(e);
  // 二级框打开时, 只有真正命中详情行才接管滚轮
  if (shelfManager.hasOpenContent()) {
    // 二级内容管理器。
    var cl = shelfManager.getContentList();
    if (cl) {
      // 二级行命中。
      var rowHit = cl.raycastRows(rc);
      // 面板射线命中。
      var panelHit = !rowHit && cl.raycastPanel ? cl.raycastPanel(rc) : null;
      // 屏幕坐标面板命中回退。
      var panelScreenHit = !rowHit && !panelHit && cl.screenContainsPanel ? cl.screenContainsPanel(e.clientX, e.clientY) : false;
      if (!rowHit && !panelHit && !panelScreenHit) return;
      e.preventDefault(); e.stopImmediatePropagation();
      cl.scrollBy(e.deltaY > 0 ? 1 : -1);
      return;
    }
  }
  // 当前歌单架模式。
  var mode = shelfManager.getMode();
  // 当前滚轮是否落在歌单架区域。
  var inShelfArea = false;
  // 歌单架是否允许滚动交互。
  var canScrollShelf = shelfManager.canInteract && shelfManager.canInteract();
  // 自动隐藏侧栏是否处于可交互状态。
  var shelfPreviewActive = shelfAutoHiddenInputReady();
  // 滚轮位置是否命中卡片。
  var cardWheelHit = canScrollShelf ? pointerCardHit(rc, e, mode === 'side' && !shelfPinnedOpen && shelfAlwaysVisible() ? 18 : undefined) : null;
  if (canScrollShelf && e.shiftKey && (mode !== 'side' || shelfPinnedOpen || shelfPreviewActive || shelfAlwaysVisible())) inShelfArea = true;
  else if (canScrollShelf && mode === 'side') {
    // 侧边模式根据固定、常显和预览状态决定是否接管滚轮。
    if (shelfPinnedOpen) inShelfArea = isShelfWheelZone(e) || !!cardWheelHit;
    else if (shelfAlwaysVisible()) inShelfArea = !!cardWheelHit;
    else if (shelfPreviewActive) inShelfArea = isShelfWheelZone(e) || !!cardWheelHit;
  }
  else if (canScrollShelf && mode === 'stage' && cardWheelHit) inShelfArea = true;
  if (inShelfArea) {
    // 接管滚轮后阻止主粒子或页面处理。
    e.preventDefault();
    e.stopImmediatePropagation();
    shelfManager.scrollBy(e.deltaY > 0 ? 1 : -1);
  }
}, { passive: false, capture: true });

// 键盘 / 全局事件
// 判断按键是否属于自由相机控制键。
function isFreeCameraControlCode(code) {
  return /^(KeyW|KeyA|KeyS|KeyD|KeyQ|KeyE|Space|ShiftLeft|ShiftRight|ControlLeft|ControlRight)$/.test(code);
}
// 尝试消费自由相机键盘事件。
function consumeFreeCameraKeyEvent(e, isDown) {
  if (isTypingTarget(e.target)) return false;
  if (isDown && e.code === 'KeyR') {
    // R 用于切换自由相机。
    e.preventDefault();
    e.stopImmediatePropagation();
    if (e.repeat) return true;
    toggleFreeCamera();
    return true;
  }
  if (!freeCamera || !freeCamera.active) return false;
  if (isDown && e.code === 'KeyK') {
    // 自由相机开启时 K 重置自由相机位置。
    e.preventDefault();
    e.stopImmediatePropagation();
    resetFreeCameraToDefault();
    return true;
  }
  if (!isFreeCameraControlCode(e.code)) return false;
  // 自由相机移动键由这里拦截，避免触发页面其他快捷键。
  e.preventDefault();
  e.stopImmediatePropagation();
  freeCamera.keys = freeCamera.keys || {};
  freeCamera.keys[e.code] = !!isDown;
  markRenderInteraction('free-camera-key', 900);
  return true;
}
// 捕获 keydown，优先交给自由相机。
document.addEventListener('keydown', function(e){
  consumeFreeCameraKeyEvent(e, true);
}, true);
// 捕获 keyup，释放自由相机按键状态。
document.addEventListener('keyup', function(e){
  consumeFreeCameraKeyEvent(e, false);
}, true);
// 全局键盘快捷键。
document.addEventListener('keydown', function(e){
  if (isTypingTarget(e.target)) return;
  markRenderInteraction('keyboard', 700);
  if (e.code === 'KeyK') {
    // K 在普通模式下回正镜头，在自由相机锁定时重置自由相机。
    e.preventDefault();
    if (freeCamera && (freeCamera.active || freeCamera.locked)) resetFreeCameraToDefault();
    else {
      recenterCamera();
      showToast('镜头已回正');
    }
    return;
  }
  if (e.code === 'KeyR') {
    // R 切换自由相机。
    if (e.repeat) return;
    e.preventDefault();
    toggleFreeCamera();
    return;
  }
  if (freeCamera && freeCamera.active) {
    // 自由相机激活时，移动键不再继续传递。
    if (/^(KeyW|KeyA|KeyS|KeyD|KeyQ|KeyE|Space|ShiftLeft|ShiftRight|ControlLeft|ControlRight)$/.test(e.code)) {
      e.preventDefault();
      e.stopImmediatePropagation();
      freeCamera.keys[e.code] = true;
      return;
    }
  }
  if (!shelfManager) return;
  // 方括号和翻页键控制歌单架上下步进。
  if (e.code === 'BracketRight' || e.code === 'PageDown') shelfManager.next();
  else if (e.code === 'BracketLeft' || e.code === 'PageUp') shelfManager.prev();
});
// 全局 keyup 兜底释放自由相机按键。
document.addEventListener('keyup', function(e){
  if (!freeCamera || !freeCamera.keys) return;
  if (/^(KeyW|KeyA|KeyS|KeyD|KeyQ|KeyE|Space|ShiftLeft|ShiftRight|ControlLeft|ControlRight)$/.test(e.code)) {
    freeCamera.keys[e.code] = false;
  }
});
// 窗口失焦时清空自由相机按键状态，避免按键卡住。
window.addEventListener('blur', function(){
  if (freeCamera && freeCamera.keys) freeCamera.keys = {};
});


// ===== js/06-api-search.js =====

// ============================================================
//  API 助手
// ============================================================
// 转义 HTML 文本，供动态插入面板时避免标签被解释。
function escHtml(s){ var d = document.createElement('div'); d.textContent = s; return d.innerHTML; }
// 判断事件目标是否是可输入文本的控件。
function isTypingTarget(target) {
  if (!target) return false;
  // 标签名统一转大写。
  var tag = String(target.tagName || '').toUpperCase();
  if (tag === 'INPUT' || tag === 'TEXTAREA' || tag === 'SELECT') return true;
  return !!(target.isContentEditable || (target.closest && target.closest('[contenteditable="true"]')));
}
// 判断封面地址是否为内联或 blob 地址。
function isInlineCoverSrc(src) {
  return typeof src === 'string' && (/^data:image\//i.test(src) || /^blob:/i.test(src));
}
// 判断封面地址是否是可直接代理或加载的 HTTP(S) 地址。
function isProxyableCoverUrl(url) {
  return /^https?:\/\//i.test(String(url || ''));
}
// 生成封面代理地址；当前桥接模式下 HTTP(S) 直接返回。
function coverProxySrc(url) {
  if (!url) return '';
  if (isInlineCoverSrc(url)) return url;
  return isProxyableCoverUrl(url) ? url : '';
}
// 给封面 URL 添加或替换指定尺寸参数。
function coverUrlWithSize(url, size) {
  if (!url || isInlineCoverSrc(url) || !/^https?:\/\//i.test(url)) return url || '';
  if (!size) return url;
  // 网易/QQ 常用的尺寸参数格式。
  var param = 'param=' + size + 'y' + size;
  if (/[?&]param=\d+y\d+/i.test(url)) return url.replace(/([?&])param=\d+y\d+/i, '$1' + param);
  return url + (url.indexOf('?') >= 0 ? '&' : '?') + param;
}
// 从歌曲对象中提取封面地址并按需请求尺寸。
function songCoverSrc(song, size) {
  var cover = song && (song.cover || song.coverUrl || song.picUrl || song.albumCover || song.albumImg || song.img || song.image || song.cover_url);
  return cover ? coverUrlWithSize(cover, size) : '';
}
// 转义可用于 CSS background-image 的 URL 片段。
function cssImageUrl(url) {
  return String(url || '').replace(/\\/g, '\\\\').replace(/"/g, '%22');
}
// 获取当前正在展示封面的歌曲。
function currentCoverSong() {
  if (currentIdx >= 0 && playQueue[currentIdx]) return playQueue[currentIdx];
  return null;
}
// 浅克隆歌曲对象，避免调用方直接修改原队列对象。
function cloneSong(song){ return Object.assign({}, song); }
// 将秒数格式化为 m:ss 或 h:mm:ss。
function formatProgramTime(sec) {
  sec = Math.max(0, Number(sec) || 0);
  // 小时。
  var h = Math.floor(sec / 3600);
  // 分钟。
  var m = Math.floor((sec % 3600) / 60);
  // 秒。
  var s = Math.floor(sec % 60);
  return h ? (h + ':' + String(m).padStart(2, '0') + ':' + String(s).padStart(2, '0')) : (m + ':' + String(s).padStart(2, '0'));
}

// 判断歌曲来源 key，默认按网易云处理。
function songProviderKey(song) {
  if (song && (song.provider === 'qq' || song.source === 'qq' || song.type === 'qq')) return 'qq';
  return 'netease';
}



// ===== js/07-audio-queue-lyrics.js =====

// 确保 UI 音效使用的 AudioContext 可用。
function ensureUiSfxContext() {
  // 浏览器 AudioContext 构造函数。
  var AudioContextCtor = window.AudioContext || window.webkitAudioContext;
  if (!AudioContextCtor) return null;
  // 首次使用或上下文被关闭时重新创建。
  if (!uiSfxCtx || uiSfxCtx.state === 'closed') uiSfxCtx = new AudioContextCtor();
  // 用户手势后尝试恢复 suspended 状态。
  if (uiSfxCtx.state === 'suspended' && uiSfxCtx.resume) uiSfxCtx.resume().catch(function(){});
  return uiSfxCtx;
}

// 播放歌单架选择移动时的短促 UI 音效。
function playShelfSelectTick(direction, variant) {
  // 当前时间戳。
  var nowMs = performance.now();
  // 行和卡片使用不同最小触发间隔，避免滚轮高速时音效过密。
  var minGap = variant === 'row' ? 36 : 42;
  if (nowMs - lastShelfSelectSfxAt < minGap) return;
  // UI 音效上下文。
  var ctx = ensureUiSfxContext();
  if (!ctx) return;
  // 记录最近播放时间。
  lastShelfSelectSfxAt = nowMs;
  // 移动方向。
  var dir = direction < 0 ? -1 : 1;
  // 上下移动使用轻微不同音高。
  var pitch = dir > 0 ? 1.035 : 0.965;
  // 行音效比卡片音效略轻。
  var rowScale = variant === 'row' ? 0.74 : 1.0;
  // 音效音量跟随当前播放器音量。
  var volumeScale = 0.38 + Math.max(0, Math.min(1, targetVolume == null ? 0.65 : targetVolume)) * 0.62;
  // 音效开始时间。
  var t = ctx.currentTime + 0.002;
  // 输出增益节点。
  var out = ctx.createGain();
  out.gain.setValueAtTime(0.0001, t);
  out.gain.linearRampToValueAtTime(0.058 * rowScale * volumeScale, t + 0.002);
  out.gain.exponentialRampToValueAtTime(0.0001, t + 0.082);
  out.connect(ctx.destination);

  // 音频采样率。
  var sampleRate = ctx.sampleRate || 44100;
  // 噪声样本长度。
  var len = Math.max(1, Math.floor(sampleRate * 0.034));
  // 噪声缓冲区。
  var buf = ctx.createBuffer(1, len, sampleRate);
  // 噪声通道数据。
  var data = buf.getChannelData(0);
  for (var i = 0; i < len; i++) {
    // 噪声包络。
    var e = Math.pow(1 - i / len, 4.2);
    data[i] = (Math.random() * 2 - 1) * e;
  }
  // 噪声源。
  var noise = ctx.createBufferSource();
  noise.buffer = buf;
  // 高频滤波器。
  var hp = ctx.createBiquadFilter();
  hp.type = 'highpass';
  hp.frequency.setValueAtTime(4200 * pitch, t);
  // 带通滤波器突出点击质感。
  var bp = ctx.createBiquadFilter();
  bp.type = 'bandpass';
  bp.frequency.setValueAtTime(8400 * pitch, t);
  bp.Q.setValueAtTime(7.2, t);
  // 噪声增益。
  var ng = ctx.createGain();
  ng.gain.setValueAtTime(0.56, t);
  noise.connect(hp);
  hp.connect(bp);
  bp.connect(ng);
  ng.connect(out);
  noise.start(t);
  noise.stop(t + 0.040);

  // 创建一个短振荡器点击层。
  function clickOsc(type, freq, delay, dur, gainValue, bend) {
    // 振荡器。
    var osc = ctx.createOscillator();
    // 振荡器增益。
    var g = ctx.createGain();
    // 开始时间。
    var start = t + delay;
    // 结束时间。
    var end = start + dur;
    osc.type = type;
    osc.frequency.setValueAtTime(freq * pitch, start);
    osc.frequency.exponentialRampToValueAtTime(freq * pitch * (bend || 0.72), end);
    g.gain.setValueAtTime(0.0001, start);
    g.gain.linearRampToValueAtTime(gainValue, start + 0.002);
    g.gain.exponentialRampToValueAtTime(0.0001, end);
    osc.connect(g);
    g.connect(out);
    osc.start(start);
    osc.stop(end + 0.004);
  }

  // 叠加多个短促音层，形成清脆选择反馈。
  clickOsc('triangle', 720, 0.000, 0.030, 0.18, 0.70);
  clickOsc('square', 2180, 0.004, 0.022, 0.30, 0.86);
  clickOsc('triangle', 4200, 0.011, 0.018, 0.18, 0.94);
  clickOsc('square', 7100, 0.018, 0.012, 0.070, 0.98);
  // 音效结束后断开输出节点。
  setTimeout(function(){
    try { out.disconnect(); } catch (_) {}
  }, 160);
}

// 将当前目标音量写入 audio 元素。
function applyVolumeToAudio() {
  if (audio) {
    audio.muted = false;
    audio.volume = targetVolume;
  }
}

// 根据 targetVolume 刷新音量滑块、数值和图标。
function updateVolumeUi() {
  // 音量滑块。
  var slider = document.getElementById('volume-slider');
  // 音量百分比文本。
  var value = document.getElementById('volume-value');
  // 音量图标。
  var icon = document.getElementById('volume-icon');
  // 音量控件外层。
  var wrap = document.getElementById('volume-control');
  // 当前音量百分比。
  var pct = Math.round(targetVolume * 100);
  if (slider && Math.abs(parseFloat(slider.value) - targetVolume) > 0.001) slider.value = targetVolume;
  if (value) value.textContent = pct + '%';
  if (wrap) wrap.classList.toggle('muted', targetVolume <= 0.01);
  if (icon) {
    // 根据音量区间切换静音、低音量和高音量图标。
    icon.innerHTML = targetVolume <= 0.01
      ? '<polygon points="11 5 6 9 2 9 2 15 6 15 11 19 11 5"/><line x1="17" y1="9" x2="22" y2="14"/><line x1="22" y1="9" x2="17" y2="14"/>'
      : targetVolume < 0.45
        ? '<polygon points="11 5 6 9 2 9 2 15 6 15 11 19 11 5"/><path d="M15 10.5a2 2 0 0 1 0 3"/>'
        : '<polygon points="11 5 6 9 2 9 2 15 6 15 11 19 11 5"/><path d="M15 9.5a4 4 0 0 1 0 5"/><path d="M18 7a7 7 0 0 1 0 10"/>';
  }
}

// 设置播放器音量并同步宿主。
function setVolume(value, silent) {
  // 音量归一化到 0..1。
  var next = Math.max(0, Math.min(1, Number(value) || 0));
  targetVolume = next;
  if (next > 0.01) lastNonZeroVolume = next;
  applyVolumeToAudio();
  updateVolumeUi();
  sendEchoHostCommand('volume', { value: next });
  if (!silent) showToast('音量 ' + Math.round(next * 100) + '%');
}
// 通过键盘快捷键按步进调整音量。
function adjustVolumeByKeyboard(delta) {
  // 音量步长。
  var step = Number(delta) || 0;
  if (!step) return;
  setVolume(clampRange(targetVolume + step, 0, 1), false);
}

// 保持音量浮层打开。
function keepVolumePanelOpen() {
  // 音量控件外层。
  var wrap = document.getElementById('volume-control');
  if (volumeCloseTimer) { clearTimeout(volumeCloseTimer); volumeCloseTimer = null; }
  if (wrap) wrap.classList.add('open');
}

// 延迟关闭音量浮层。
function closeVolumePanelSoon() {
  // 音量控件外层。
  var wrap = document.getElementById('volume-control');
  if (volumeCloseTimer) clearTimeout(volumeCloseTimer);
  volumeCloseTimer = setTimeout(function(){
    volumeCloseTimer = null;
    if (wrap) wrap.classList.remove('open');
  }, 520);
}

// 将滚轮事件转换为音量变化量。
function volumeWheelDelta(e) {
  if (!e || !isFinite(e.deltaY) || e.deltaY === 0) return 0;
  // 限制单次滚轮幅度，避免高精度触控板一次改变过多。
  var normalized = Math.sign(e.deltaY) * Math.min(Math.abs(e.deltaY), 120);
  // macOS 和 Windows 滚轮方向习惯差异。
  var platform = String(navigator.platform || '').toLowerCase();
  var direction = platform.indexOf('mac') >= 0 ? 1 : -1;
  return (normalized / 120) * 0.05 * direction;
}

// 计算滚轮调整后的目标音量。
function targetVolumeAfterWheel(e) {
  // 滚轮音量增量。
  var delta = volumeWheelDelta(e);
  if (!delta) return targetVolume;
  return clampRange(targetVolume + delta, 0, 1);
}

// 静音和恢复上次非零音量。
function toggleMute(e) {
  if (e) {
    e.preventDefault();
    e.stopPropagation();
  }
  setVolume(targetVolume > 0.01 ? 0 : (lastNonZeroVolume || 0.8), true);
}

// 绑定音量控件事件。
function bindVolumeControls() {
  // 音量滑块。
  var slider = document.getElementById('volume-slider');
  // 音量控件外层。
  var wrap = document.getElementById('volume-control');
  if (wrap) {
    wrap.addEventListener('mouseenter', keepVolumePanelOpen);
    wrap.addEventListener('mouseleave', closeVolumePanelSoon);
  }
  if (slider) {
    slider.addEventListener('focus', keepVolumePanelOpen);
    slider.addEventListener('blur', closeVolumePanelSoon);
  }
  document.addEventListener('click', function(e){
    if (!wrap) return;
    if (!wrap.contains(e.target)) {
      // 点击外部时立即关闭音量浮层。
      if (volumeCloseTimer) { clearTimeout(volumeCloseTimer); volumeCloseTimer = null; }
      wrap.classList.remove('open');
    }
  });
  updateVolumeUi();
  applyVolumeToAudio();
}

// ============================================================
//  播放队列
// ============================================================
// 规范化发送给宿主的歌曲对象。
function hostCommandSong(song) {
  if (!song) return null;
  // 克隆歌曲，避免补字段时修改原对象。
  var cloned = typeof cloneSong === 'function' ? cloneSong(song) : Object.assign({}, song);
  // 宿主需要的歌曲 id。
  var id = cloned.id != null && cloned.id !== '' ? cloned.id : (cloned.hash || cloned.trackId || '');
  // hash 兼容字段。
  var hash = cloned.hash || id;
  if (id == null || id === '') return null;
  // 统一写入宿主需要的字段。
  cloned.id = String(id);
  cloned.hash = String(hash || id);
  cloned.title = cloned.title || cloned.name || '未知歌曲';
  cloned.name = cloned.name || cloned.title;
  cloned.artist = cloned.artist || '未知歌手';
  cloned.coverUrl = cloned.coverUrl || cloned.cover || '';
  cloned.cover = cloned.cover || cloned.coverUrl || '';
  cloned.duration = Number(cloned.duration || 0);
  return cloned;
}
// 向 EchoMusic 宿主发送桥接命令。
function sendEchoHostCommand(name, payload) {
  window.__echoBridgeCommand(name, payload || {});
}
// 请求宿主播放指定歌曲。
function requestHostPlaySong(song) {
  // 规范化后的歌曲载荷。
  var payloadSong = hostCommandSong(song);
  if (!payloadSong) return false;
  sendEchoHostCommand('play-song', { song: payloadSong });
  return true;
}
// 请求宿主将指定歌曲插入下一首。
function requestHostPlayNextSong(song) {
  // 规范化后的歌曲载荷。
  var payloadSong = hostCommandSong(song);
  if (!payloadSong) return false;
  sendEchoHostCommand('queue-play-next-song', { song: payloadSong });
  return true;
}
// 将二级内容中的歌曲发送为下一首。
function queueDetailSongNext(song) {
  if (!song) return;
  requestHostPlayNextSong(song);
  if (typeof showToast === 'function') showToast('已发送下一首: ' + (song.name || ''));
}
// 请求宿主把队列指定索引设置为下一首。
function requestHostPlayNextIndex(i) {
  i = Number(i);
  if (!isFinite(i) || i < 0 || i >= playQueue.length) return;
  sendEchoHostCommand('queue-play-next-index', { index: i });
}
// 首次播放是否已经完成。
var firstPlayDone = false;

// 请求宿主播放队列中的指定索引。
async function playQueueAt(idx, opts) {
  opts = opts || {};
  hideLoading();
  forcePlaybackControlsInteractive();
  // 目标队列索引。
  idx = Number(idx);
  if (!isFinite(idx) || idx < 0) return false;
  sendEchoHostCommand('play-index', { index: idx });
  return false;
}
// 请求宿主切换播放/暂停。
async function togglePlay() {
  if (playToggleBusy) return;
  playToggleBusy = true;
  forcePlaybackControlsInteractive();
  hideLoading();
  sendEchoHostCommand('toggle-play');
  playToggleBusy = false;
}
// 设置播放按钮图标。
function setPlayIcon(p) {
  document.getElementById('play-icon').innerHTML = p
    ? '<rect x="6" y="4" width="4" height="16"/><rect x="14" y="4" width="4" height="16"/>'
    : '<path d="M8 5v14l11-7z"/>';
}
// 请求宿主播放下一首。
function nextTrack() {
  playToggleBusy = false;
  forcePlaybackControlsInteractive();
  sendEchoHostCommand('next');
}
// 请求宿主播放上一首。
function prevTrack() {
  playToggleBusy = false;
  forcePlaybackControlsInteractive();
  sendEchoHostCommand('prev');
}
// 请求宿主切换随机模式。
function shuffleQueue() {
  sendEchoHostCommand('set-mode', { mode: 'random' });
}
// 请求宿主清空播放队列。
function clearQueue() {
  sendEchoHostCommand('queue-clear');
}
// 请求宿主移除播放队列中的指定索引。
function removeFromQueue(idx) {
  // 队列索引归一化为数字。
  idx = Number(idx);
  if (!isFinite(idx) || idx < 0) return;
  sendEchoHostCommand('queue-remove-index', { index: idx });
}
// 将播放模式 key 转换为用户可读标签。
function playModeLabel(mode) {
  return { loop: '顺序循环', shuffle: '随机播放', single: '单曲循环' }[mode] || '顺序循环';
}

// 根据播放模式返回对应的 SVG 图标片段。
function playModeIconMarkup(mode) {
  if (mode === 'shuffle') {
    // 随机播放图标。
    return '<path d="M16 3h5v5"/><path d="M4 20 21 3"/><path d="M21 16v5h-5"/><path d="M15 15l6 6"/><path d="M4 4l5 5"/>';
  }
  if (mode === 'single') {
    // 单曲循环图标。
    return '<path d="M17 2l4 4-4 4"/><path d="M3 11V9a4 4 0 0 1 4-4h14"/><path d="M7 22l-4-4 4-4"/><path d="M21 13v2a4 4 0 0 1-4 4H3"/><path d="M12 9v6"/><path d="M10.5 10.5 12 9l1.5 1.5"/>';
  }
  // 默认顺序循环图标。
  return '<path d="M17 2l4 4-4 4"/><path d="M3 11V9a4 4 0 0 1 4-4h14"/><path d="M7 22l-4-4 4-4"/><path d="M21 13v2a4 4 0 0 1-4 4H3"/>';
}

// 刷新播放模式按钮的文本、图标、可访问标签和切换动画。
function updatePlayModeButton(animate) {
  // 当前播放模式标签。
  var label = playModeLabel(playMode);
  // 播放模式文字胶囊。
  var chip = document.getElementById('play-mode-chip');
  // 播放模式按钮。
  var btn = document.getElementById('play-mode-btn');
  // 播放模式图标容器。
  var icon = document.getElementById('play-mode-icon');
  if (chip) chip.textContent = label;
  if (btn) {
    // 用 dataset、title 和 aria-label 同步当前模式。
    btn.dataset.mode = playMode;
    btn.title = label;
    btn.setAttribute('aria-label', label);
    btn.classList.toggle('active', playMode !== 'loop');
  }
  if (icon) icon.innerHTML = playModeIconMarkup(playMode);
  if (!animate || !btn) return;
  if (window.gsap) {
    // 使用 GSAP 做按钮弹跳和外扩光圈。
    window.gsap.killTweensOf(btn);
    if (icon) window.gsap.killTweensOf(icon);
    window.gsap.timeline({ defaults: { overwrite: true } })
      .fromTo(btn, { scale: 0.86, rotate: -8 }, { scale: 1.12, rotate: 4, duration: 0.16, ease: 'power2.out' })
      .to(btn, { scale: 1, rotate: 0, duration: 0.34, ease: 'back.out(2.1)' });
    window.gsap.fromTo(btn,
      { boxShadow: '0 0 0 0 rgba(255,63,85,.36)' },
      { boxShadow: '0 0 0 14px rgba(255,63,85,0)', duration: 0.58, ease: 'sine.out', overwrite: false, onComplete: function(){ window.gsap.set(btn, { clearProps: 'boxShadow' }); } }
    );
    if (icon) window.gsap.fromTo(icon, { y: 4, autoAlpha: 0.32, rotate: -22, scale: 0.74 }, { y: 0, autoAlpha: 1, rotate: 0, scale: 1, duration: 0.42, ease: 'expo.out', overwrite: true });
  } else {
    // 无 GSAP 时使用 CSS class 触发一次过渡动画。
    btn.classList.remove('mode-switching');
    void btn.offsetWidth;
    btn.classList.add('mode-switching');
    setTimeout(function(){ btn.classList.remove('mode-switching'); }, 460);
  }
}

// 请求宿主循环切换播放模式。
function cyclePlayMode() {
  sendEchoHostCommand('cycle-mode');
}
// 初始化播放模式按钮为当前状态，不播放动画。
updatePlayModeButton(false);

// 控制条玻璃位移图的尺寸缓存状态。
var controlGlassState = { key: '' };
// 归一化控制条玻璃色散偏移量。
function normalizeControlGlassChromaticOffset(value) {
  // 用户或配置传入值。
  var n = Number(value);
  if (!isFinite(n)) n = fxDefaults.controlGlassChromaticOffset;
  return clampRange(n, 0, 140);
}
// 将控制条玻璃色散偏移写入 SVG filter。
function applyControlGlassChromaticOffset() {
  if (!fx) return;
  // 先把运行时配置夹到合法范围。
  fx.controlGlassChromaticOffset = normalizeControlGlassChromaticOffset(fx.controlGlassChromaticOffset);
  // 控制条玻璃滤镜节点。
  var filter = document.getElementById('mineradio-control-glass-filter');
  if (!filter) return;
  // 红蓝通道横向偏移量。
  var dx = String(-Math.round(fx.controlGlassChromaticOffset));
  filter.querySelectorAll('feOffset').forEach(function(node){
    node.setAttribute('dx', dx);
    node.setAttribute('dy', '0');
  });
}
// 检测当前浏览器是否适合启用 SVG backdrop-filter 玻璃位移。
function supportsControlGlassSvgFilter() {
  try {
    // Safari 和 Firefox 对该滤镜组合兼容性不足，直接禁用。
    var ua = navigator.userAgent || '';
    if ((/Safari/.test(ua) && !/Chrome/.test(ua)) || /Firefox/.test(ua)) return false;
    // 使用 style 赋值探测浏览器是否接受 url filter。
    var div = document.createElement('div');
    div.style.backdropFilter = 'url(#mineradio-control-glass-filter)';
    return div.style.backdropFilter !== '';
  } catch (e) {
    return false;
  }
}
// 生成控制条玻璃位移贴图 data URL。
function generateControlGlassDisplacementMap(width, height, radius) {
  // 位移贴图宽度。
  width = Math.max(240, Math.round(width || 400));
  // 位移贴图高度。
  height = Math.max(48, Math.round(height || 92));
  // 圆角半径。
  radius = Math.max(12, Math.round(radius || 50));
  // 边缘折射带宽度比例。
  var borderWidth = 0.07;
  // 边缘实际宽度。
  var edge = Math.min(width, height) * (borderWidth * 0.5);
  // 内部稳定区域宽度。
  var innerW = Math.max(1, width - edge * 2);
  // 内部稳定区域高度。
  var innerH = Math.max(1, height - edge * 2);
  // 位移图 SVG 内容。
  var svg = '<svg viewBox="0 0 ' + width + ' ' + height + '" xmlns="http://www.w3.org/2000/svg">' +
    '<defs>' +
    '<linearGradient id="glass-red" x1="100%" y1="0%" x2="0%" y2="0%"><stop offset="0%" stop-color="#0000"/><stop offset="100%" stop-color="red"/></linearGradient>' +
    '<linearGradient id="glass-blue" x1="0%" y1="0%" x2="0%" y2="100%"><stop offset="0%" stop-color="#0000"/><stop offset="100%" stop-color="blue"/></linearGradient>' +
    '</defs>' +
    '<rect x="0" y="0" width="' + width + '" height="' + height + '" fill="black"/>' +
    '<rect x="0" y="0" width="' + width + '" height="' + height + '" rx="' + radius + '" fill="url(#glass-red)"/>' +
    '<rect x="0" y="0" width="' + width + '" height="' + height + '" rx="' + radius + '" fill="url(#glass-blue)" style="mix-blend-mode:difference"/>' +
    '<rect x="' + edge.toFixed(2) + '" y="' + edge.toFixed(2) + '" width="' + innerW.toFixed(2) + '" height="' + innerH.toFixed(2) + '" rx="' + radius + '" fill="hsl(0 0% 50% / 1)" style="filter:blur(11px)"/>' +
    '</svg>';
  return 'data:image/svg+xml,' + encodeURIComponent(svg);
}
// 根据元素实际尺寸刷新玻璃位移贴图。
function updateGlassDisplacementMapForElement(el, img, stateKey) {
  if (!el || !img) return;
  // 目标元素屏幕尺寸。
  var rect = el.getBoundingClientRect();
  if (rect.width < 2 || rect.height < 2) return;
  // 读取元素圆角半径，保证位移图和真实外形一致。
  var radius = parseFloat(getComputedStyle(el).borderRadius) || 24;
  // 当前尺寸状态键。
  var key = Math.round(rect.width) + 'x' + Math.round(rect.height) + ':' + Math.round(radius);
  if (key === controlGlassState[stateKey]) return;
  controlGlassState[stateKey] = key;
  // 新的位移图 data URL。
  var href = generateControlGlassDisplacementMap(rect.width, rect.height, radius);
  img.setAttribute('href', href);
  try { img.setAttributeNS('http://www.w3.org/1999/xlink', 'href', href); } catch (e) {}
}
// 刷新底部控制条玻璃位移贴图。
function updateControlGlassDisplacementMap() {
  updateGlassDisplacementMapForElement(
    document.getElementById('bottom-bar'),
    document.getElementById('control-glass-map'),
    'key'
  );
}
// 初始化底部控制条玻璃表面滤镜和尺寸监听。
function initControlGlassSurface() {
  if (supportsControlGlassSvgFilter()) document.documentElement.classList.add('control-glass-svg-ok');
  applyControlGlassChromaticOffset();
  updateControlGlassDisplacementMap();
  // 底部控制条节点。
  var bar = document.getElementById('bottom-bar');
  if (window.ResizeObserver && bar) {
    // 控制条尺寸变化时重建位移贴图。
    var ro = new ResizeObserver(function(){
      requestAnimationFrame(updateControlGlassDisplacementMap);
    });
    if (bar) ro.observe(bar);
  }
  // 窗口尺寸变化也可能影响控制条宽度。
  window.addEventListener('resize', function(){
    requestAnimationFrame(updateControlGlassDisplacementMap);
  });
}

// 为底部播放控制按钮绑定悬停、按压和点击动画。
function bindPlayerControlAnimations() {
  if (!window.gsap) return;
  document.querySelectorAll('#bottom-bar .ctrl-btn').forEach(function(btn){
    if (!btn || btn.dataset.controlAnimBound === '1') return;
    // 防止重复绑定同一个按钮。
    btn.dataset.controlAnimBound = '1';
    // 当前按钮是否为主播放按钮。
    var isPlay = btn.id === 'play-btn';
    // 按钮内的图标动画目标。
    var iconTarget = btn.querySelector('svg,.lyrics-word-icon');
    // 判断当前按钮是否可播放动画。
    function canAnimate() {
      return !btn.disabled && !btn.classList.contains('busy');
    }
    // 指针悬停进入动画。
    function hoverIn(e) {
      if (!canAnimate() || (e && e.pointerType === 'touch')) return;
      window.gsap.to(btn, { y: -2, scale: isPlay ? 1.07 : 1.08, duration: 0.20, ease: 'power2.out', overwrite: 'auto' });
      if (iconTarget) window.gsap.to(iconTarget, { scale: isPlay ? 1.08 : 1.10, duration: 0.22, ease: 'power2.out', overwrite: 'auto' });
    }
    // 指针离开或失焦时恢复按钮状态。
    function hoverOut() {
      window.gsap.to(btn, { y: 0, scale: 1, rotate: 0, duration: 0.26, ease: 'power2.out', overwrite: 'auto' });
      if (iconTarget) window.gsap.to(iconTarget, { scale: 1, rotate: 0, duration: 0.22, ease: 'power2.out', overwrite: 'auto' });
    }
    // 按下按钮时的压缩反馈。
    function pressDown() {
      if (!canAnimate()) return;
      window.gsap.to(btn, { y: 0, scale: isPlay ? 0.91 : 0.90, duration: 0.10, ease: 'power2.out', overwrite: 'auto' });
      if (iconTarget) window.gsap.to(iconTarget, { scale: 0.88, duration: 0.10, ease: 'power2.out', overwrite: 'auto' });
    }
    // 释放按钮时根据是否仍悬停决定回弹目标。
    function release(e) {
      if (!canAnimate()) return;
      // 触摸释放不按 hover 处理。
      var hovered = e && e.pointerType !== 'touch' && btn.matches(':hover');
      window.gsap.to(btn, { y: hovered ? -2 : 0, scale: hovered ? (isPlay ? 1.07 : 1.08) : 1, duration: 0.24, ease: 'back.out(1.9)', overwrite: 'auto' });
      if (iconTarget) window.gsap.to(iconTarget, { scale: hovered ? 1.06 : 1, duration: 0.22, ease: 'back.out(1.8)', overwrite: 'auto' });
    }
    // 点击时播放外扩脉冲反馈。
    function clickPulse() {
      if (!canAnimate() || btn.id === 'play-mode-btn') return;
      // 主播放按钮使用更大的脉冲。
      var pulseSize = isPlay ? 18 : 10;
      // 主播放按钮使用品牌红，其它按钮使用浅白。
      var pulseColor = isPlay ? 'rgba(255,63,85,.34)' : 'rgba(255,255,255,.22)';
      window.gsap.killTweensOf(btn, 'boxShadow');
      window.gsap.fromTo(btn,
        { boxShadow: '0 0 0 0 ' + pulseColor },
        { boxShadow: '0 0 0 ' + pulseSize + 'px rgba(255,63,85,0)', duration: isPlay ? 0.58 : 0.42, ease: 'sine.out', overwrite: false, onComplete: function(){ window.gsap.set(btn, { clearProps: 'boxShadow' }); } }
      );
      if (iconTarget) window.gsap.fromTo(iconTarget, { rotate: isPlay ? 0 : -5 }, { rotate: 0, duration: 0.34, ease: 'elastic.out(1,0.55)', overwrite: 'auto' });
    }
    // 绑定指针、鼠标和焦点事件。
    btn.addEventListener('pointerenter', hoverIn);
    btn.addEventListener('pointerleave', hoverOut);
    btn.addEventListener('pointercancel', hoverOut);
    btn.addEventListener('mousedown', function(e){ e.preventDefault(); });
    btn.addEventListener('pointerdown', pressDown);
    btn.addEventListener('pointerup', release);
    btn.addEventListener('click', clickPulse);
    btn.addEventListener('focus', function(){ hoverIn(); });
    btn.addEventListener('blur', hoverOut);
  });
}

// 清理底部播放控制按钮的焦点和动画残留状态。
function clearPlayerControlFocusState(reason) {
  try {
    document.querySelectorAll('#bottom-bar .ctrl-btn').forEach(function(btn){
      if (!btn) return;
      // 如果按钮当前获得焦点，主动移除焦点。
      if (document.activeElement === btn) btn.blur();
      btn.classList.remove('focus-visible');
      if (window.gsap) {
        // 清理按钮本体动画并恢复基础状态。
        window.gsap.killTweensOf(btn);
        window.gsap.set(btn, { y: 0, scale: 1, rotate: 0, clearProps: 'boxShadow' });
        // 清理按钮图标动画。
        var iconTarget = btn.querySelector('svg,.lyrics-word-icon');
        if (iconTarget) {
          window.gsap.killTweensOf(iconTarget);
          window.gsap.set(iconTarget, { scale: 1, rotate: 0 });
        }
      } else {
        // 无 GSAP 时清空内联样式。
        btn.style.transform = '';
        btn.style.boxShadow = '';
      }
    });
  } catch (e) {
    console.warn('[ControlFocusClear]', reason || 'unknown', e);
  }
}

// ============================================================
//  歌词
// ============================================================
// 判断歌词文本是否属于“无歌词”占位内容。
function isNoLyricText(text) {
  // 去除空白和常见标点后再比较。
  var compact = String(text || '').replace(/\s+/g, '').replace(/[，,。.!！?？、~～]/g, '');
  return !compact ||
    compact === '纯音乐请欣赏' ||
    compact === '暂无歌词' ||
    compact === '暂无歌词敬请期待' ||
    compact === '此歌曲为没有填词的纯音乐请您欣赏';
}
// 渲染歌词入口；当前版本由 3D 舞台歌词系统接管。
function renderLyrics() {
  // v8: 歌词渲染由 stageLyrics 在每帧 tickLyricsParticles 里推动
  clearStageLyrics();
}
// 切换舞台歌词显示状态。
function toggleLyricsPanel(force) {
  // force 为布尔值时直接写入，否则取反当前状态。
  if (force === false) fx.particleLyrics = false;
  else if (force === true) fx.particleLyrics = true;
  else fx.particleLyrics = !fx.particleLyrics;
  if (fx.particleLyrics) {
    // 开启时创建歌词粒子系统。
    createLyricsParticles();
    showToast('歌词已开启');
  } else {
    // 关闭时清理舞台歌词。
    clearStageLyrics();
    showToast('歌词已关闭');
  }
  lyricsVisible = fx.particleLyrics;
}
// 歌词高亮更新入口；当前由舞台歌词逐帧逻辑接管。
function updateLyricsHighlight() { /* v8: 由 tickLyricsParticles 接管 */ }



// ===== js/08-panels-files-controls.js =====

// ============================================================
//  播放列表面板
// ============================================================
// 给列表中可见项播放入场动画。
function animateListItems(container, selector, opts) {
  if (!container || !window.gsap) return;
  opts = opts || {};
  // 候选列表项。
  var items = Array.prototype.slice.call(container.querySelectorAll(selector));
  if (!items.length) return;
  // 最大动画项数，避免超长队列一次性创建大量 tween。
  var limit = opts.limit || 18;
  // 本次参与动画的目标项。
  var targets = items.slice(0, limit);
  window.gsap.killTweensOf(targets);
  window.gsap.fromTo(targets, {
    autoAlpha: 0,
    y: opts.y == null ? 8 : opts.y,
    x: opts.x == null ? -6 : opts.x
  }, {
    autoAlpha: 1,
    y: 0,
    x: 0,
    duration: opts.duration || 0.22,
    stagger: opts.stagger || 0.012,
    ease: opts.ease || 'power2.out',
    force3D: true,
    overwrite: true
  });
}
// 将滚动容器平滑滚动到指定子项附近。
function smoothScrollToItem(scroller, item, opts) {
  if (!scroller || !item) return;
  opts = opts || {};
  // 目标 scrollTop，align 控制目标项在视口中的垂直位置。
  var target = item.offsetTop - Math.max(0, (scroller.clientHeight - item.offsetHeight) * (opts.align == null ? 0.42 : opts.align));
  // 目标滚动位置夹在容器可滚动范围内。
  target = Math.max(0, Math.min(target, Math.max(0, scroller.scrollHeight - scroller.clientHeight)));
  if (window.gsap) {
    // 如果容器绑定了平滑滚轮，则同步其内部目标，避免两个 tween 抢滚动。
    if (typeof scroller.__syncSmoothWheelTarget === 'function') scroller.__syncSmoothWheelTarget(target);
    window.gsap.killTweensOf(scroller);
    window.gsap.to(scroller, { scrollTop: target, duration: opts.duration || 0.30, ease: opts.ease || 'power2.out', overwrite: true });
  } else if (scroller.scrollTo) {
    scroller.scrollTo({ top: target, behavior: 'smooth' });
  } else {
    scroller.scrollTop = target;
  }
}
// 给滚动容器绑定 GSAP 平滑滚轮。
function bindSmoothWheelScroll(scroller) {
  if (!scroller || scroller.__smoothWheelBound) return;
  // 防重复绑定标记。
  scroller.__smoothWheelBound = true;
  // 当前平滑滚动目标。
  var targetTop = scroller.scrollTop;
  // 当前滚动 tween。
  var tween = null;
  // 供外部同步目标滚动位置。
  scroller.__syncSmoothWheelTarget = function(top){
    if (tween) {
      tween.kill();
      tween = null;
    }
    targetTop = isFinite(top) ? top : scroller.scrollTop;
  };
  scroller.addEventListener('wheel', function(e){
    if (!window.gsap || e.ctrlKey) return;
    // 最大可滚动距离。
    var max = Math.max(0, scroller.scrollHeight - scroller.clientHeight);
    if (max <= 0 || Math.abs(e.deltaY) <= Math.abs(e.deltaX)) return;
    // 滚轮增量。
    var delta = e.deltaY;
    if (e.deltaMode === 1) delta *= 18;
    else if (e.deltaMode === 2) delta *= scroller.clientHeight;
    // 当前滚动基准。
    var current = tween ? targetTop : scroller.scrollTop;
    // 下一个目标位置。
    var next = Math.max(0, Math.min(max, current + delta));
    if (next === current && ((delta < 0 && scroller.scrollTop <= 0) || (delta > 0 && scroller.scrollTop >= max - 1))) {
      targetTop = scroller.scrollTop;
      return;
    }
    e.preventDefault();
    targetTop = next;
    if (tween) tween.kill();
    // 平滑滚到目标位置。
    tween = window.gsap.to(scroller, {
      scrollTop: targetTop,
      duration: 0.24,
      ease: 'power2.out',
      overwrite: true,
      onComplete: function(){
        tween = null;
        targetTop = scroller.scrollTop;
      }
    });
  }, { passive: false });
  // 用户或脚本直接滚动时同步目标位置。
  scroller.addEventListener('scroll', function(){
    if (!tween) targetTop = scroller.scrollTop;
  }, { passive: true });
}
// 给队列相关面板绑定一次平滑滚轮。
function bindSmoothQueueScrolling() {
  if (smoothWheelScrollBound) return;
  // 全局防重复绑定标记。
  smoothWheelScrollBound = true;
  [
    'mini-queue-list',
    'fx-panel',
    'playlist-panel'
  ].forEach(function(id){
    bindSmoothWheelScroll(document.getElementById(id));
  });
}
// 面板显示后播放列表入场动画，并可滚到当前项。
function animateVisiblePanelList(listEl, selector, scroller, activeSelector, opts) {
  if (!listEl) return;
  opts = opts || {};
  requestAnimationFrame(function(){
    animateListItems(listEl, selector, { x: -8, y: 6, stagger: 0.01, duration: 0.20, limit: 16 });
    // 当前激活项。
    var active = activeSelector ? listEl.querySelector(activeSelector) : null;
    if (active && scroller && opts.scrollActive !== false) smoothScrollToItem(scroller, active, { duration: 0.32 });
  });
}
// 切换左侧播放列表面板显示状态。
function togglePlaylistPanel(force) {
  // 左侧播放列表面板。
  var el = document.getElementById('playlist-panel');
  if (force === false) el.classList.remove('show');
  else if (force === true) el.classList.add('show');
  else el.classList.toggle('show');
  if (el.classList.contains('show')) {
    // 打开面板时播放轻微入场动画。
    if (window.gsap) window.gsap.fromTo(el, { x: -12, autoAlpha: 0.92 }, { x: 0, autoAlpha: 1, duration: 0.22, ease: 'power2.out', overwrite: true });
    scheduleUiWarmTask(function(){
      // 面板打开后刷新延迟渲染的队列内容。
      flushDeferredQueuePanel('playlist-panel-open');
      switchPlaylistTab('queue');
      animateVisiblePanelList(document.getElementById('queue-list'), '.queue-item', el, '.queue-item.now', { scrollActive: false });
    }, 180);
  }
}
// 将播放列表面板常开状态应用到 DOM。
function applyPlaylistPanelPinState(openPanel) {
  // 左侧播放列表面板。
  var panel = document.getElementById('playlist-panel');
  // 常开按钮。
  var btn = document.getElementById('playlist-pin-btn');
  if (panel) {
    panel.classList.toggle('pinned', !!playlistPanelPinned);
    if (playlistPanelPinned || openPanel) {
      // 常开或主动打开时保留面板 peek 状态。
      panel.dataset.preserveTabOnOpen = '1';
      setPeek(panel, true, 'pl');
    }
  }
  if (btn) {
    // 同步按钮激活态和提示文案。
    btn.classList.toggle('active', !!playlistPanelPinned);
    btn.title = playlistPanelPinned ? '取消常开队列' : '常开队列';
  }
}
// 设置左侧播放列表面板是否常开。
function setPlaylistPanelPinned(on, silent) {
  playlistPanelPinned = !!on;
  saveBooleanPreference(PLAYLIST_PANEL_PIN_STORE_KEY, playlistPanelPinned);
  applyPlaylistPanelPinState(playlistPanelPinned);
  if (!silent) showToast(playlistPanelPinned ? '左侧队列已常开' : '左侧队列已恢复自动隐藏');
}
// 切换左侧播放列表面板常开状态。
function togglePlaylistPanelPinned() {
  setPlaylistPanelPinned(!playlistPanelPinned);
}
// 将左侧队列面板滚动到当前播放项。
function scrollPlaylistPanelToCurrent() {
  // 左侧面板滚动容器。
  var panel = document.getElementById('playlist-panel');
  // 队列列表容器。
  var list = document.getElementById('queue-list');
  if (!panel || !list || queueViewTab !== 'queue') return;
  // 节流，避免频繁切歌或重复打开时持续滚动。
  var now = performance.now();
  if (panel.__lastCurrentScrollAt && now - panel.__lastCurrentScrollAt < 650) return;
  panel.__lastCurrentScrollAt = now;
  requestAnimationFrame(function(){
    smoothScrollToItem(panel, list.querySelector('.queue-item.now'), { duration: 0.28, align: 0.34 });
  });
}
// 切换播放列表面板标签；当前只保留队列标签。
function switchPlaylistTab(tab) {
  queueViewTab = 'queue';
  // 队列内容面板。
  var queuePane = document.getElementById('queue-pane');
  if (queuePane) queuePane.style.display = '';
  animateVisiblePanelList(document.getElementById('queue-list'), '.queue-item', document.getElementById('playlist-panel'), '.queue-item.now');
}
// 设置底部迷你队列弹层打开状态。
function setMiniQueueOpen(open) {
  miniQueueOpen = !!open;
  // 迷你队列弹层。
  var pop = document.getElementById('mini-queue-popover');
  // 迷你队列按钮。
  var btn = document.getElementById('mini-queue-btn');
  if (pop) pop.classList.toggle('show', miniQueueOpen);
  if (btn) btn.classList.toggle('active', miniQueueOpen);
  if (miniQueueOpen) {
    // 弹层打开后在下一帧渲染队列，避免布局状态未更新。
    var seq = ++miniQueueRenderSeq;
    requestAnimationFrame(function(){
      if (seq !== miniQueueRenderSeq || !miniQueueOpen) return;
      renderMiniQueuePanel({ animate: true, scrollCurrent: true });
    });
    revealBottomControls(1300);
  }
}
// 切换迷你队列弹层。
function toggleMiniQueue(e) {
  if (e) { e.preventDefault(); e.stopPropagation(); }
  setMiniQueueOpen(!miniQueueOpen);
}
// 关闭迷你队列弹层。
function closeMiniQueue() {
  setMiniQueueOpen(false);
}
// 渲染底部迷你队列弹层。
function renderMiniQueuePanel(opts) {
  opts = opts || {};
  // 迷你队列列表节点。
  var $list = document.getElementById('mini-queue-list');
  // 迷你队列计数节点。
  var $count = document.getElementById('mini-queue-count');
  if (!$list || !$count) return;
  // 队列总数。
  var total = playQueue.length;
  $count.textContent = total ? (total + ' 首' + (currentIdx >= 0 ? ' · 正在播放 ' + (currentIdx + 1) : '')) : '0 首';
  if (!miniQueueOpen && !opts.animate && !opts.scrollCurrent) return;
  if (!total) {
    // 空队列占位。
    $list.innerHTML = '<div class="mini-queue-empty">队列为空</div>';
    return;
  }
  // 生成迷你队列 HTML。
  $list.innerHTML = playQueue.map(function(song, i){
    // 当前歌曲缩略封面。
    var thumb = songCoverSrc(song, 60);
    // 封面图片或占位块。
    var imgTag = thumb ? '<img src="' + thumb + '" alt="" loading="lazy" decoding="async" onerror="this.style.opacity=0.2">' : '<div class="mini-queue-cover"></div>';
    return '<div class="mini-queue-item' + (i === currentIdx ? ' now' : '') + '" onclick="playQueueAt(' + i + ')">' +
      imgTag +
      '<div class="mini-queue-info"><div class="mini-queue-name">' + escHtml(song.name) + '</div><div class="mini-queue-sub">' + escHtml(song.artist || '') + '</div></div>' +
      '<button class="mini-queue-remove mini-queue-next" onclick="event.stopPropagation();requestHostPlayNextIndex(' + i + ')" title="下一首播放">下</button>' +
      '<button class="mini-queue-remove" onclick="event.stopPropagation();removeFromQueue(' + i + ')" title="移除">×</button>' +
    '</div>';
  }).join('');
  if (opts.animate || opts.scrollCurrent) {
    requestAnimationFrame(function(){
      // 弹层打开时播放可见项入场动画。
      if (opts.animate) animateListItems($list, '.mini-queue-item', { x: 0, y: 6, stagger: 0.01, duration: 0.20, limit: 16 });
      // 按需滚到当前播放项。
      if (opts.scrollCurrent) smoothScrollToItem($list, $list.querySelector('.mini-queue-item.now'), { duration: 0.30, align: 0.42 });
    });
  }
}
// 点击底部栏外部时关闭迷你队列。
document.addEventListener('click', function(e){
  if (miniQueueOpen && !(e.target && e.target.closest && e.target.closest('#bottom-bar'))) closeMiniQueue();
});
// 初始化队列相关滚动容器的平滑滚动。
bindSmoothQueueScrolling();
// 初始化通用弹层背景点击关闭逻辑。
bindModalBackdropClose();
// 渲染左侧播放队列面板。
function renderQueuePanel(opts) {
  opts = opts || {};
  // 主队列列表节点。
  var $ql = document.getElementById('queue-list');
  // 渲染序号，用于避免旧动画调度作用到新内容。
  var seq = ++queueRenderSeq;
  if (!playQueue.length) {
    // 空队列占位。
    $ql.innerHTML = '<div style="text-align:center;padding:24px 0;color:rgba(255,255,255,.32);font-size:11.5px">队列为空</div>';
    renderMiniQueuePanel();
    return;
  }
  // 生成主队列 HTML。
  $ql.innerHTML = playQueue.map(function(song, i){
    // 当前歌曲缩略封面。
    var thumb = songCoverSrc(song, 60);
    // 封面图片或占位块。
    var imgTag = thumb ? '<img src="' + thumb + '" alt="" loading="lazy" decoding="async" onerror="this.style.opacity=0.2">' : '<div style="width:38px;height:38px;border-radius:6px;background:rgba(255,255,255,.06);flex-shrink:0"></div>';
    return '<div class="queue-item' + (i === currentIdx ? ' now' : '') + '" onclick="playQueueAt(' + i + ')">' +
      imgTag +
      '<div class="qi-info"><div class="qi-name">' + escHtml(song.name) + '</div><div class="qi-sub">' + escHtml(song.artist || '未知歌手') + '</div></div>' +
      '<div class="qi-act">' +
        '<button class="queue-next" onclick="event.stopPropagation();requestHostPlayNextIndex(' + i + ')" title="下一首播放">下</button>' +
        '<button onclick="event.stopPropagation();removeFromQueue(' + i + ')" title="移除">×</button>' +
      '</div>' +
    '</div>';
  }).join('');
  // 只允许最新一次渲染调度播放入场动画。
  if (opts.animate && seq === queueRenderSeq) animateVisiblePanelList($ql, '.queue-item', document.getElementById('playlist-panel'), '.queue-item.now');
  // 主队列变化时同步刷新迷你队列。
  renderMiniQueuePanel({ scrollCurrent: miniQueueOpen });
}
// 进度条
// 归一化歌曲时长，兼容毫秒和秒两种单位。
function normalizePlaybackDurationSeconds(value) {
  // 原始时长数值。
  var raw = Number(value);
  if (!isFinite(raw) || raw <= 0) return 0;
  // 大于 1000 的值按毫秒处理。
  return raw > 1000 ? raw / 1000 : raw;
}
// 从歌曲对象读取播放时长。
function playbackDurationFromSong(song) {
  if (!song) return 0;
  return normalizePlaybackDurationSeconds(song.duration || song.durationMs || song.dt || 0);
}
// 获取当前播放总时长，优先使用 audio 元素真实时长。
function getPlaybackDurationSeconds() {
  if (audio && isFinite(audio.duration) && audio.duration > 0) return audio.duration;
  return playbackDurationFromSong(currentCoverSong());
}
// 获取当前播放进度秒数。
function getPlaybackCurrentSeconds() {
  return audio && isFinite(audio.currentTime) && audio.currentTime > 0 ? audio.currentTime : 0;
}
// 设置进度条填充和滑块位置。
function setProgressVisual(percent) {
  // 进度百分比。
  percent = clampRange(percent || 0, 0, 100);
  // 进度填充节点。
  var fill = document.getElementById('progress-fill');
  // 进度滑块节点。
  var thumb = document.getElementById('progress-thumb');
  if (fill) fill.style.width = percent + '%';
  if (thumb) thumb.style.left = percent + '%';
}
// 刷新播放进度 UI。
function updatePlaybackProgressUi() {
  // 当前歌曲总时长。
  var durationSec = getPlaybackDurationSeconds();
  // 当前播放秒数。
  var currentSec = getPlaybackCurrentSeconds();
  if (durationSec > 0 && currentSec > durationSec) currentSec = durationSec;
  setProgressVisual(durationSec > 0 ? (currentSec / durationSec * 100) : 0);
  // 时间显示节点。
  var timeDisplay = document.getElementById('time-display');
  if (timeDisplay) timeDisplay.textContent = formatProgramTime(currentSec) + ' / ' + (durationSec > 0 ? formatProgramTime(durationSec) : '0:00');
}
// 本地刷新播放进度和歌词高亮状态，不向宿主请求数据。
setInterval(function(){
  if (!audio) { updatePlaybackProgressUi(); return; }
  updatePlaybackProgressUi();
  if (audio.currentTime) updateLyricsHighlight();
}, 200);

// ============================================================
//  控制台 — 预设卡片 + 主滑块 + 开关 + 三态
// ============================================================
// 视觉预设卡片的展示文案。
var presetMeta = [
  { name: 'emily专辑封面',  desc: '封面粒子 · 快速入场' },
  { name: '滚筒', desc: '隧道 · 沉浸感' },
  { name: '星球',  desc: '星球 · 雕塑感' },
  { name: '虚空', desc: '无粒子 · 自定义背景' },
  { name: '唱片', desc: '唱片 · 圆形封面' },
  { name: '星河', desc: '壁纸粒子 · 音乐律动' },
  { name: '安魂', desc: '骷髅·YUI7W', descHtml: '骷髅·<span class="pc-yui7w">YUI7W</span>' },
];
// 视觉预设卡片对应的 SVG 图标片段。
var presetIcons = [
  '<svg width="18" height="18" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><path d="M3 14c3-2 5-2 8 0s5 2 8 0M3 10c3-2 5-2 8 0s5 2 8 0M3 18c3-2 5-2 8 0s5 2 8 0"/></svg>',
  '<svg width="18" height="18" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><circle cx="12" cy="12" r="9"/><circle cx="12" cy="12" r="5"/><circle cx="12" cy="12" r="1.5" fill="currentColor"/></svg>',
  '<svg width="18" height="18" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><circle cx="12" cy="12" r="7"/><path d="M5 12a7 7 0 0 0 14 0"/></svg>',
  '<svg width="18" height="18" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8"><circle cx="12" cy="12" r="7"/><path d="M8.8 8.8l6.4 6.4"/></svg>',
  '<svg width="18" height="18" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8"><circle cx="12" cy="12" r="8.5"/><circle cx="12" cy="12" r="4.4"/><path d="M16.5 5.2c2.1.9 3.4 2.4 4 4.5"/><path d="M18.8 3.2l1.5 4.8"/></svg>',
  '<svg width="18" height="18" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8"><path d="M3 15c2.2-4.4 4.4-4.4 6.6 0s4.4 4.4 6.6 0S20.6 10.6 23 15"/><path d="M3 9c2.2 2.2 4.4 2.2 6.6 0s4.4-2.2 6.6 0S20.6 11.2 23 9"/><circle cx="12" cy="12" r="1.7" fill="currentColor"/></svg>',
  '<svg width="18" height="18" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.75" stroke-linecap="round" stroke-linejoin="round"><path d="M10 3.2h4v6.2h4.2v3.8H14v7.6h-4v-7.6H5.8V9.4H10z"/></svg>',
];
// 控制台预设卡片展示顺序。
var presetDisplayOrder = [0, 6, 5, 4, 2, 1, 3];
// 歌词颜色预设列表。
var lyricColorPresets = [
  { name:'雾蓝', color:'#a9b8c8' },
  { name:'银蓝', color:'#9db8cf' },
  { name:'冰川', color:'#7ec8d8' },
  { name:'青绿', color:'#66d2b5' },
  { name:'松针', color:'#7fa894' },
  { name:'月白', color:'#d7d2c4' },
  { name:'岩金', color:'#c3ae7c' },
  { name:'琥珀', color:'#d9a45f' },
  { name:'暮粉', color:'#c78aa4' },
  { name:'玫红', color:'#d76a8d' },
  { name:'烟紫', color:'#9b83d3' },
  { name:'电紫', color:'#8d70ff' },
  { name:'靛蓝', color:'#5e78d8' },
  { name:'海蓝', color:'#3c9fe0' },
  { name:'霓青', color:'#28c5c3' },
  { name:'夜绿', color:'#245c49' },
  { name:'酒红', color:'#6d1f35' },
  { name:'墨黑', color:'#111318' },
];
// 用户视觉存档 localStorage key。
var USER_FX_ARCHIVE_STORE_KEY = 'mineradio-user-fx-archives-v1';
// 用户视觉存档导出文件类型标记。
var USER_FX_ARCHIVE_EXPORT_TYPE = 'mineradio-user-fx-archive';
// 用户视觉存档结构版本。
var USER_FX_ARCHIVE_SCHEMA = 1;
// 生成默认用户视觉存档名。
function defaultUserFxArchiveName(index) {
  return '存档 ' + (index + 1);
}
// 归一化用户视觉存档名。
function normalizeUserFxArchiveName(name, index) {
  // 合并空白并去掉首尾空格。
  name = String(name || '').replace(/\s+/g, ' ').trim();
  if (!name) name = defaultUserFxArchiveName(index);
  // 存档名最长 18 个字符。
  return name.slice(0, 18);
}
// 从存档对象读取数字字段并夹到指定范围。
function archiveNumber(raw, key, fallback, min, max) {
  // 原始字段值。
  var value = raw && raw[key] != null ? Number(raw[key]) : fallback;
  if (!isFinite(value)) value = fallback;
  return clampRange(value, min, max);
}
// 从存档对象读取枚举字段并用正则校验。
function archiveMode(raw, key, pattern, fallback) {
  // 原始枚举值。
  var value = String(raw && raw[key] != null ? raw[key] : fallback);
  return pattern.test(value) ? value : fallback;
}
// 归一化用户视觉存档快照，丢弃非法字段并补齐默认值。
function normalizeFxArchiveSnapshot(raw) {
  if (!raw || typeof raw !== 'object') return null;
  // 存档中的视觉预设索引。
  var savedPreset = normalizeVisualPresetIndex(raw.preset, DEFAULT_PLAYBACK_VISUAL_PRESET);
  if (savedPreset === 3 && raw.visualPresetSchema !== VISUAL_PRESET_SCHEMA) savedPreset = 5;
  return {
    // 当前视觉预设 schema。
    visualPresetSchema: VISUAL_PRESET_SCHEMA,
    // 归一化后的视觉预设索引。
    preset: savedPreset,
    intensity: archiveNumber(raw, 'intensity', fxDefaults.intensity, 0.2, 1.6),
    cinemaShake: archiveNumber(raw, 'cinemaShake', fxDefaults.cinemaShake, 0, 1.8),
    depth: archiveNumber(raw, 'depth', fxDefaults.depth, 0.2, 1.8),
    coverResolution: normalizeCoverResolution(raw.coverResolution),
    point: archiveNumber(raw, 'point', fxDefaults.point, 0.5, 2.2),
    speed: archiveNumber(raw, 'speed', fxDefaults.speed, 0.2, 2.5),
    twist: archiveNumber(raw, 'twist', fxDefaults.twist, 0, 0.6),
    color: archiveNumber(raw, 'color', fxDefaults.color, 0.5, 2.0),
    scatter: archiveNumber(raw, 'scatter', fxDefaults.scatter, 0, 0.5),
    bgFade: archiveNumber(raw, 'bgFade', fxDefaults.bgFade, 0, 1.2),
    bloomStrength: archiveNumber(raw, 'bloomStrength', fxDefaults.bloomStrength, 0, 1.6),
    lyricGlowStrength: archiveNumber(raw, 'lyricGlowStrength', fxDefaults.lyricGlowStrength, 0, 0.85),
    lyricScale: archiveNumber(raw, 'lyricScale', fxDefaults.lyricScale, 0.35, 1.65),
    lyricOffsetX: archiveNumber(raw, 'lyricOffsetX', fxDefaults.lyricOffsetX, -2.0, 2.0),
    lyricOffsetY: archiveNumber(raw, 'lyricOffsetY', fxDefaults.lyricOffsetY, -1.2, 1.35),
    lyricOffsetZ: archiveNumber(raw, 'lyricOffsetZ', fxDefaults.lyricOffsetZ, -1.6, 1.6),
    lyricTiltX: archiveNumber(raw, 'lyricTiltX', fxDefaults.lyricTiltX, -42, 42),
    lyricTiltY: archiveNumber(raw, 'lyricTiltY', fxDefaults.lyricTiltY, -42, 42),
    lyricCameraLock: !!raw.lyricCameraLock,
    lyricColorMode: raw.lyricColorMode === 'custom' ? 'custom' : 'auto',
    lyricColor: normalizeHexColor(raw.lyricColor || fxDefaults.lyricColor),
    lyricHighlightMode: raw.lyricHighlightMode === 'custom' ? 'custom' : 'auto',
    lyricHighlightColor: normalizeHexColor(raw.lyricHighlightColor || fxDefaults.lyricHighlightColor),
    lyricGlowLinked: raw.lyricGlowLinked !== false,
    lyricGlowColor: normalizeHexColor(raw.lyricGlowColor || fxDefaults.lyricGlowColor),
    lyricFont: normalizeLyricFontKey(raw.lyricFont),
    lyricLetterSpacing: archiveNumber(raw, 'lyricLetterSpacing', fxDefaults.lyricLetterSpacing, -0.04, 0.18),
    lyricLineHeight: archiveNumber(raw, 'lyricLineHeight', fxDefaults.lyricLineHeight, 0.86, 1.35),
    lyricWeight: archiveNumber(raw, 'lyricWeight', fxDefaults.lyricWeight, 500, 900),
    visualTintMode: raw.visualTintMode === 'custom' ? 'custom' : 'auto',
    visualTintColor: normalizeHexColor(raw.visualTintColor || fxDefaults.visualTintColor),
    uiAccentColor: normalizeHexColor(raw.uiAccentColor || fxDefaults.uiAccentColor, fxDefaults.uiAccentColor),
    visualIconColor: normalizeHexColor(raw.visualIconColor || fxDefaults.visualIconColor, fxDefaults.visualIconColor),
    backgroundColorMode: raw.backgroundColorMode === 'custom' || raw.backgroundColorCustom ? 'custom' : 'cover',
    backgroundColor: normalizeHexColor(raw.backgroundColor || fxDefaults.backgroundColor, fxDefaults.backgroundColor),
    backgroundOpacity: archiveNumber(raw, 'backgroundOpacity', fxDefaults.backgroundOpacity, 0, 1),
    controlGlassChromaticOffset: archiveNumber(raw, 'controlGlassChromaticOffset', fxDefaults.controlGlassChromaticOffset, 0, 140),
    backgroundColorCustom: raw.backgroundColorMode === 'custom' || !!raw.backgroundColorCustom,
    floatLayer: !!raw.floatLayer,
    cinema: raw.cinema !== false,
    edge: !!raw.edge,
    aiDepth: !!raw.aiDepth,
    bloom: !!raw.bloom,
    lyricGlow: raw.lyricGlow !== false,
    lyricGlowBeat: raw.lyricGlowBeat !== false,
    lyricGlowParticles: !!raw.lyricGlowParticles,
    performanceBackground: normalizePerformanceBackgroundMode(raw.performanceBackground, raw.liveBackgroundKeep === true),
    performanceQuality: normalizePerformanceQuality(raw.performanceQuality),
    liveBackgroundKeep: normalizePerformanceBackgroundMode(raw.performanceBackground, raw.liveBackgroundKeep === true) === 'keep',
    particleLyrics: raw.particleLyrics !== false,
    backCover: !!raw.backCover,
    shelf: archiveMode(raw, 'shelf', /^(off|side|stage)$/, fxDefaults.shelf),
    shelfCameraMode: archiveMode(raw, 'shelfCameraMode', /^(dynamic|static)$/, fxDefaults.shelfCameraMode),
    shelfPresence: archiveMode(raw, 'shelfPresence', /^(auto|always)$/, fxDefaults.shelfPresence),
    shelfSize: archiveNumber(raw, 'shelfSize', fxDefaults.shelfSize, 0.65, 1.45),
    shelfOffsetX: archiveNumber(raw, 'shelfOffsetX', fxDefaults.shelfOffsetX, -1.2, 1.2),
    shelfOffsetY: archiveNumber(raw, 'shelfOffsetY', fxDefaults.shelfOffsetY, -0.9, 0.9),
    shelfOffsetZ: archiveNumber(raw, 'shelfOffsetZ', fxDefaults.shelfOffsetZ, -0.9, 0.9),
    shelfAngleY: archiveNumber(raw, 'shelfAngleY', fxDefaults.shelfAngleY, -30, 30),
    shelfAngleYManual: raw.shelfAngleYManual === true,
    shelfOpacity: archiveNumber(raw, 'shelfOpacity', fxDefaults.shelfOpacity, 0.25, 1),
    shelfBgOpacity: archiveNumber(raw, 'shelfBgOpacity', fxDefaults.shelfBgOpacity, 0.25, 0.98),
    shelfAccentColor: normalizeHexColor(raw.shelfAccentColor || fxDefaults.shelfAccentColor, fxDefaults.shelfAccentColor)
  };
}
// 从 localStorage 读取用户视觉存档列表。
function readUserFxArchives() {
  // 原始存档数组。
  var raw = [];
  try {
    raw = JSON.parse(localStorage.getItem(USER_FX_ARCHIVE_STORE_KEY) || '[]') || [];
  } catch (e) {
    raw = [];
  }
  if (!Array.isArray(raw)) raw = [];
  return raw.map(function(slot, index){
    // 单个存档槽原始对象。
    slot = slot && typeof slot === 'object' ? slot : {};
    // 归一化快照。
    var snapshot = normalizeFxArchiveSnapshot(slot.snapshot);
    return {
      name: normalizeUserFxArchiveName(slot.name, index),
      createdAt: Number(slot.createdAt) || (snapshot ? (Number(slot.savedAt) || Date.now()) : 0),
      savedAt: snapshot ? (Number(slot.savedAt) || Date.now()) : 0,
      snapshot: snapshot
    };
  }).filter(function(slot){
    // 过滤完全空的槽位。
    return !!(slot.snapshot || slot.savedAt || slot.createdAt);
  });
}
// 保存用户视觉存档列表到 localStorage。
function saveUserFxArchives() {
  try {
    localStorage.setItem(USER_FX_ARCHIVE_STORE_KEY, JSON.stringify(userFxArchives));
  } catch (e) {
    showToast('用户存档保存失败，本地存储空间可能不足');
  }
}
// 判断本机是否已经存在用户视觉存档。
function hasStoredUserFxArchives() {
  try {
    return localStorage.getItem(USER_FX_ARCHIVE_STORE_KEY) != null;
  } catch (e) {
    return true;
  }
}
// 从打包默认快照创建初始用户存档槽。
function createPackagedDefaultUserFxArchiveSlot() {
  return {
    name: normalizeUserFxArchiveName(PACKAGED_DEFAULT_USER_FX_ARCHIVE_NAME, 0),
    createdAt: PACKAGED_DEFAULT_USER_FX_ARCHIVE_EXPORTED_AT,
    savedAt: PACKAGED_DEFAULT_USER_FX_ARCHIVE_SAVED_AT,
    snapshot: normalizeFxArchiveSnapshot(clonePackagedDefaultFxSnapshot())
  };
}
// 格式化用户存档保存时间。
function formatUserArchiveTime(ts) {
  ts = Number(ts) || 0;
  if (!ts) return '空槽位';
  // 距离当前时间的毫秒差。
  var diff = Date.now() - ts;
  if (diff < 60000) return '刚刚保存';
  if (diff < 3600000) return Math.max(1, Math.round(diff / 60000)) + ' 分钟前';
  // 保存时间。
  var d = new Date(ts);
  // 两位数补零。
  function pad(v) { return String(v).padStart(2, '0'); }
  return pad(d.getMonth() + 1) + '-' + pad(d.getDate()) + ' ' + pad(d.getHours()) + ':' + pad(d.getMinutes());
}
// 捕获当前 fx 为可保存的用户视觉快照。
function captureFxArchiveSnapshot() {
  return normalizeFxArchiveSnapshot(Object.assign({ visualPresetSchema: VISUAL_PRESET_SCHEMA }, fx));
}
// 应用已保存的歌词色板状态到舞台歌词。
function applySavedLyricPaletteState() {
  if (!stageLyrics) return;
  setStageLyricPalette(fx.lyricColorMode === 'custom'
    ? lyricPaletteFromHex(fx.lyricColor)
    : (stageLyrics.coverPalette || stageLyrics.palette));
  // 同步歌词颜色相关控件。
  updateLyricColorControls();
  updateLyricHighlightControls();
  updateLyricGlowControls();
}
// 应用一个用户视觉存档快照。
function applyFxArchiveSnapshot(snapshot) {
  // 归一化后的存档数据。
  var data = normalizeFxArchiveSnapshot(snapshot);
  if (!data) return false;
  // 目标预设单独处理。
  var targetPreset = data.preset;
  Object.keys(data).forEach(function(key){
    if (key === 'visualPresetSchema' || key === 'preset') return;
    fx[key] = data[key];
  });
  // 保持开发锁相关状态合法。
  normalizeDevelopmentLockedFxState();
  setPreset(targetPreset, { silent: true, preserveCamera: false, skipTransition: false, noSave: true, commitPlaybackPreset: true });
  // 应用所有依赖存档字段的视觉模块。
  applyCoverParticleResolution(fx.coverResolution, { reload: true });
  if (fx.floatLayer) createFloatLayer(); else destroyFloatLayer();
  setParticleLyricsSilently(fx.particleLyrics);
  if (fx.backCover) createBackCoverLayer(); else destroyBackCoverLayer();
  if (fx.aiDepth) {
    aiDepthFailUntil = 0;
    queueAIDepthForCurrentCover(true);
  }
  setShelfMode(fx.shelf);
  if (shelfManager && shelfManager.rebuild) shelfManager.rebuild(true);
  if (shelfManager && shelfManager.refreshTheme) shelfManager.refreshTheme();
  updateFxInputs();
  applySavedLyricPaletteState();
  refreshCurrentLyricStyle();
  applyWallpaperModeState(true);
  updateRenderPowerClasses();
  applyRendererPowerMode();
  saveLyricLayout();
  return true;
}
// 启动时是否已经存在用户存档。
var hadStoredUserFxArchives = hasStoredUserFxArchives();
// 当前用户视觉存档列表。
var userFxArchives = readUserFxArchives();
if (!hadStoredUserFxArchives) {
  // 首次启动时写入打包默认用户存档。
  userFxArchives = [createPackagedDefaultUserFxArchiveSlot()];
  saveUserFxArchives();
}
// 当前正在编辑名称的用户存档索引。
var userFxArchiveEditing = -1;
// 渲染用户视觉存档网格。
function renderUserFxArchives() {
  // 用户存档网格容器。
  var grid = document.getElementById('user-archive-grid');
  if (!grid) return;
  grid.innerHTML = userFxArchives.map(function(slot, index){
    // 当前槽位是否有快照。
    var hasSave = !!slot.snapshot;
    // 当前槽位是否正在改名。
    var editing = userFxArchiveEditing === index;
    // 名称区域 HTML。
    var nameHtml = editing
      ? '<input class="user-archive-input" id="user-archive-input-' + index + '" type="text" maxlength="18" value="' + escHtml(slot.name) + '" onkeydown="handleUserFxArchiveRenameKey(event,' + index + ')">'
      : '<div class="user-archive-name" title="' + escHtml(slot.name) + '">' + escHtml(slot.name) + '</div>';
    // 操作按钮 HTML。
    var actionsHtml = editing
      ? '<button type="button" onclick="commitUserFxArchiveRename(' + index + ')">确定</button>' +
        '<button type="button" onclick="cancelUserFxArchiveRename()">取消</button>'
      : '<button type="button" onclick="applyUserFxArchive(' + index + ')"' + (hasSave ? '' : ' disabled') + '>应用</button>' +
        '<button type="button" onclick="saveUserFxArchive(' + index + ')">保存</button>' +
        '<button type="button" onclick="renameUserFxArchive(' + index + ')">命名</button>';
    return '<div class="user-archive-slot' + (hasSave ? ' has-save' : '') + '" data-slot="' + index + '">' +
      nameHtml +
      '<div class="user-archive-meta">' + formatUserArchiveTime(slot.savedAt) + '</div>' +
      '<div class="user-archive-actions">' +
        actionsHtml +
      '</div>' +
    '</div>';
  }).join('');
  if (userFxArchiveEditing >= 0) {
    // 改名模式进入后自动聚焦输入框。
    setTimeout(function(){
      var input = document.getElementById('user-archive-input-' + userFxArchiveEditing);
      if (input) {
        input.focus();
        input.select();
      }
    }, 0);
  }
}
// 保存当前视觉状态到指定用户存档槽。
function saveUserFxArchive(index) {
  // 目标槽位索引。
  index = clampRange(Number(index) || 0, 0, Math.max(0, userFxArchives.length - 1));
  userFxArchives[index].snapshot = captureFxArchiveSnapshot();
  userFxArchives[index].savedAt = Date.now();
  userFxArchives[index].name = normalizeUserFxArchiveName(userFxArchives[index].name, index);
  saveUserFxArchives();
  renderUserFxArchives();
  showToast('已保存到 ' + userFxArchives[index].name);
}
// 应用指定用户存档槽。
function applyUserFxArchive(index) {
  // 目标槽位索引。
  index = clampRange(Number(index) || 0, 0, Math.max(0, userFxArchives.length - 1));
  // 目标槽位。
  var slot = userFxArchives[index];
  if (!slot || !slot.snapshot) {
    showToast('这个用户存档还是空的');
    return;
  }
  if (applyFxArchiveSnapshot(slot.snapshot)) {
    showToast('已应用 ' + slot.name);
  }
}
// 进入指定用户存档槽的改名状态。
function renameUserFxArchive(index) {
  index = clampRange(Number(index) || 0, 0, Math.max(0, userFxArchives.length - 1));
  userFxArchiveEditing = index;
  renderUserFxArchives();
}
// 提交用户存档改名。
function commitUserFxArchiveRename(index) {
  index = clampRange(Number(index) || 0, 0, Math.max(0, userFxArchives.length - 1));
  // 改名输入框。
  var input = document.getElementById('user-archive-input-' + index);
  userFxArchives[index].name = normalizeUserFxArchiveName(input && input.value, index);
  userFxArchiveEditing = -1;
  saveUserFxArchives();
  renderUserFxArchives();
  showToast('已命名为 ' + userFxArchives[index].name);
}
// 取消用户存档改名。
function cancelUserFxArchiveRename() {
  userFxArchiveEditing = -1;
  renderUserFxArchives();
}
// 处理用户存档改名输入框快捷键。
function handleUserFxArchiveRenameKey(e, index) {
  if (e.key === 'Enter') {
    // Enter 提交改名。
    e.preventDefault();
    commitUserFxArchiveRename(index);
  } else if (e.key === 'Escape') {
    // Escape 取消改名。
    e.preventDefault();
    cancelUserFxArchiveRename();
  }
}

// 生成用户存档默认名称；后续增强版允许超过 4 个存档。
function defaultUserFxArchiveName(index) {
  return '用户存档 ' + (Number(index) + 1);
}
// 归一化增强版用户存档名称。
function normalizeUserFxArchiveName(name, index) {
  // 合并连续空白并去掉首尾空格。
  name = String(name || '').replace(/\s+/g, ' ').trim();
  if (!name) name = defaultUserFxArchiveName(index);
  // 增强版名称最长 28 个字符。
  return name.slice(0, 28);
}
// 按索引读取用户存档槽。
function userFxArchiveAt(index) {
  // 存档索引。
  index = Number(index);
  if (!isFinite(index)) return null;
  index = Math.floor(index);
  return index >= 0 && index < userFxArchives.length ? userFxArchives[index] : null;
}
// 渲染增强版用户视觉存档网格。
function renderUserFxArchives() {
  // 用户存档网格容器。
  var grid = document.getElementById('user-archive-grid');
  if (!grid) return;
  // 顶部工具栏 HTML。
  var toolbar =
    '<div class="user-archive-toolbar">' +
      '<div class="user-archive-note">空白新建，保存当前视觉参数；支持拖拽 JSON 导入，也可以导出为文件备份。</div>' +
      '<div class="user-archive-tools">' +
        '<button class="fx-mini-btn ghost" type="button" onclick="createUserFxArchive()">新建</button>' +
        '<button class="fx-mini-btn ghost" type="button" onclick="importUserFxArchiveFromDialog()">导入</button>' +
      '</div>' +
    '</div>';
  // 存档卡片 HTML。
  var cards = userFxArchives.map(function(slot, index){
    // 当前槽位是否有快照。
    var hasSave = !!slot.snapshot;
    // 当前槽位是否处于改名状态。
    var editing = userFxArchiveEditing === index;
    // 名称区 HTML。
    var nameHtml = editing
      ? '<input class="user-archive-input" id="user-archive-input-' + index + '" type="text" maxlength="28" value="' + escHtml(slot.name) + '" onkeydown="handleUserFxArchiveRenameKey(event,' + index + ')">'
      : '<div class="user-archive-name" title="' + escHtml(slot.name) + '">' + escHtml(slot.name) + '</div>';
    // 操作按钮 HTML。
    var actionsHtml = editing
      ? '<button type="button" onclick="commitUserFxArchiveRename(' + index + ')">确定</button>' +
        '<button type="button" onclick="cancelUserFxArchiveRename()">取消</button>'
      : '<button type="button" onclick="applyUserFxArchive(' + index + ')"' + (hasSave ? '' : ' disabled') + '>应用</button>' +
        '<button type="button" onclick="saveUserFxArchive(' + index + ')">保存</button>' +
        '<button type="button" onclick="renameUserFxArchive(' + index + ')">命名</button>' +
        '<button type="button" onclick="exportUserFxArchive(' + index + ')"' + (hasSave ? '' : ' disabled') + '>导出</button>' +
        '<button type="button" onclick="removeUserFxArchive(' + index + ')">删除</button>';
    return '<div class="user-archive-slot' + (hasSave ? ' has-save' : '') + '" data-slot="' + index + '">' +
      nameHtml +
      '<div class="user-archive-meta">' + (hasSave ? formatUserArchiveTime(slot.savedAt) : '空白存档，点击保存写入当前视觉') + '</div>' +
      '<div class="user-archive-actions">' + actionsHtml + '</div>' +
    '</div>';
  }).join('');
  // 新建空白存档卡片。
  var addCard = '<button class="user-archive-slot is-new" type="button" onclick="createUserFxArchive()"><strong>＋ 新建空白存档</strong><span class="user-archive-meta">可继续创建，不限制 4 个</span></button>';
  grid.innerHTML = toolbar + cards + addCard;
  bindUserFxArchiveDrop();
  if (userFxArchiveEditing >= 0) {
    // 改名模式下自动聚焦输入框。
    setTimeout(function(){
      var input = document.getElementById('user-archive-input-' + userFxArchiveEditing);
      if (input) {
        input.focus();
        input.select();
      }
    }, 0);
  }
}
// 创建一个新的空白用户视觉存档。
function createUserFxArchive() {
  // 新存档索引。
  var index = userFxArchives.length;
  userFxArchives.push({
    name: normalizeUserFxArchiveName('', index),
    createdAt: Date.now(),
    savedAt: 0,
    snapshot: null
  });
  userFxArchiveEditing = index;
  saveUserFxArchives();
  renderUserFxArchives();
  showToast('已新建空白用户存档');
}
// 保存当前视觉参数到指定存档槽。
function saveUserFxArchive(index) {
  // 目标存档槽。
  var slot = userFxArchiveAt(index);
  if (!slot) return;
  slot.snapshot = captureFxArchiveSnapshot();
  slot.savedAt = Date.now();
  slot.createdAt = slot.createdAt || slot.savedAt;
  slot.name = normalizeUserFxArchiveName(slot.name, index);
  saveUserFxArchives();
  renderUserFxArchives();
  showToast('已保存到 ' + slot.name);
}
// 应用指定用户存档。
function applyUserFxArchive(index) {
  // 目标存档槽。
  var slot = userFxArchiveAt(index);
  if (!slot || !slot.snapshot) {
    showToast('这个用户存档还是空白');
    return;
  }
  if (applyFxArchiveSnapshot(slot.snapshot)) showToast('已应用 ' + slot.name);
}
// 进入指定用户存档的改名状态。
function renameUserFxArchive(index) {
  if (!userFxArchiveAt(index)) return;
  userFxArchiveEditing = Math.floor(Number(index) || 0);
  renderUserFxArchives();
}
// 提交增强版用户存档改名。
function commitUserFxArchiveRename(index) {
  // 目标存档槽。
  var slot = userFxArchiveAt(index);
  if (!slot) return;
  // 改名输入框。
  var input = document.getElementById('user-archive-input-' + index);
  slot.name = normalizeUserFxArchiveName(input && input.value, index);
  slot.createdAt = slot.createdAt || Date.now();
  userFxArchiveEditing = -1;
  saveUserFxArchives();
  renderUserFxArchives();
  showToast('已命名为 ' + slot.name);
}
// 取消增强版用户存档改名。
function cancelUserFxArchiveRename() {
  userFxArchiveEditing = -1;
  renderUserFxArchives();
}
// 删除指定用户存档。
function removeUserFxArchive(index) {
  if (!userFxArchiveAt(index)) return;
  userFxArchives.splice(index, 1);
  userFxArchiveEditing = -1;
  saveUserFxArchives();
  renderUserFxArchives();
  showToast('已删除用户存档');
}
// 构建用户存档导出载荷。
function userFxArchiveExportPayload(slot) {
  return {
    type: USER_FX_ARCHIVE_EXPORT_TYPE,
    schema: USER_FX_ARCHIVE_SCHEMA,
    exportedAt: Date.now(),
    name: slot.name,
    savedAt: slot.savedAt,
    snapshot: slot.snapshot
  };
}
// 生成安全的用户存档导出文件名。
function safeArchiveFileName(name) {
  return String(name || 'Mineradio 用户存档').replace(/[\\/:*?"<>|]+/g, '-').slice(0, 48) + '.json';
}
// 将指定用户存档导出为 JSON 文件。
function exportUserFxArchive(index) {
  // 目标存档槽。
  var slot = userFxArchiveAt(index);
  if (!slot || !slot.snapshot) {
    showToast('空白存档不能导出');
    return;
  }
  // 导出载荷。
  var payload = userFxArchiveExportPayload(slot);
  // 格式化后的 JSON 文本。
  var text = JSON.stringify(payload, null, 2);
  // JSON Blob。
  var blob = new Blob([text], { type: 'application/json;charset=utf-8' });
  // 临时下载 URL。
  var url = URL.createObjectURL(blob);
  // 临时下载链接。
  var a = document.createElement('a');
  a.href = url;
  a.download = safeArchiveFileName(slot.name);
  a.click();
  setTimeout(function(){ URL.revokeObjectURL(url); }, 1000);
}
// 归一化导入的用户存档 JSON 载荷。
function normalizeImportedFxArchivePayload(payload, fileName) {
  if (!payload || typeof payload !== 'object') return null;
  // 导入文件可直接是快照，也可以是带 snapshot 的导出包。
  var snapshot = payload.snapshot ? normalizeFxArchiveSnapshot(payload.snapshot) : normalizeFxArchiveSnapshot(payload);
  if (!snapshot) return null;
  // 文件名作为名称兜底。
  var baseName = String(fileName || '').split(/[\\/]/).pop().replace(/\.json$/i, '');
  return {
    name: normalizeUserFxArchiveName(payload.name || baseName, userFxArchives.length),
    createdAt: Date.now(),
    savedAt: Number(payload.savedAt) || Date.now(),
    snapshot: snapshot
  };
}
// 从 JSON 文本导入用户视觉存档。
function importUserFxArchiveText(text, fileName) {
  // 解析后的 JSON 对象。
  var payload = null;
  try { payload = JSON.parse(String(text || '')); } catch (e) {}
  // 归一化后的存档槽。
  var slot = normalizeImportedFxArchivePayload(payload, fileName);
  if (!slot) {
    showToast('导入失败，文件不是有效的用户存档');
    return false;
  }
  userFxArchives.push(slot);
  saveUserFxArchives();
  renderUserFxArchives();
  showToast('已导入 ' + slot.name);
  return true;
}
// 打开系统文件选择框导入用户视觉存档。
function importUserFxArchiveFromDialog() {
  // 临时文件输入。
  var input = document.createElement('input');
  input.type = 'file';
  input.accept = '.json,application/json';
  input.onchange = function(){
    // 用户选择的文件。
    var file = input.files && input.files[0];
    if (file) readUserFxArchiveImportFile(file);
  };
  input.click();
}
// 读取并导入用户视觉存档文件。
function readUserFxArchiveImportFile(file) {
  if (!file || !/\.json$/i.test(file.name || '')) {
    showToast('请导入 JSON 用户存档');
    return;
  }
  // 文件读取器。
  var reader = new FileReader();
  reader.onload = function(e){ importUserFxArchiveText(e.target && e.target.result, file.name); };
  reader.onerror = function(){ showToast('导入失败'); };
  reader.readAsText(file, 'utf-8');
}
// 给用户存档网格绑定拖拽导入。
function bindUserFxArchiveDrop() {
  // 用户存档网格容器。
  var grid = document.getElementById('user-archive-grid');
  if (!grid || grid._archiveDropBound) return;
  // 防重复绑定标记。
  grid._archiveDropBound = true;
  grid.addEventListener('dragover', function(e){
    if (!e.dataTransfer || !e.dataTransfer.files || !e.dataTransfer.files.length) return;
    e.preventDefault();
    grid.classList.add('dragover');
  });
  grid.addEventListener('dragleave', function(e){
    if (!grid.contains(e.relatedTarget)) grid.classList.remove('dragover');
  });
  grid.addEventListener('drop', function(e){
    if (!e.dataTransfer || !e.dataTransfer.files || !e.dataTransfer.files.length) return;
    e.preventDefault();
    grid.classList.remove('dragover');
    // 支持一次拖入多个 JSON 文件。
    Array.prototype.forEach.call(e.dataTransfer.files, readUserFxArchiveImportFile);
  });
}

// 构建歌词颜色选择控件。
function buildLyricColorControls() {
  // 歌词颜色色板容器。
  var grid = document.getElementById('lyric-color-grid');
  if (!grid) return;
  // 自动取色按钮 HTML。
  var html = '<button class="lyric-swatch auto" type="button" data-auto="1" onclick="setLyricColorAuto()" title="封面取色">AUTO</button>';
  html += lyricColorPresets.map(function(p, i){
    return '<button class="lyric-swatch" type="button" data-color="' + p.color + '" onclick="setLyricColorPreset(' + i + ')" title="' + escHtml(p.name) + '" style="--swatch:' + p.color + '"></button>';
  }).join('');
  grid.innerHTML = html;
}
// 刷新歌词主色控件状态。
function updateLyricColorControls() {
  // 歌词颜色 input。
  var picker = document.getElementById('lyric-color-picker');
  // 歌词颜色显示文本。
  var value = document.getElementById('lyric-color-value');
  // 自动取色按钮。
  var autoBtn = document.getElementById('lyric-auto-btn');
  // 当前歌词颜色。
  var color = normalizeHexColor(fx.lyricColor);
  if (picker) picker.value = color;
  if (value) value.textContent = fx.lyricColorMode === 'custom' ? color.toUpperCase() : '封面取色';
  if (autoBtn) autoBtn.classList.toggle('active', fx.lyricColorMode !== 'custom');
  document.querySelectorAll('.lyric-swatch').forEach(function(btn){
    // 当前色块是否为自动色块。
    var isAuto = btn.dataset.auto === '1';
    // 当前色块颜色是否匹配自定义颜色。
    var isColor = normalizeHexColor(btn.dataset.color || '') === color;
    btn.classList.toggle('active', isAuto ? fx.lyricColorMode !== 'custom' : (fx.lyricColorMode === 'custom' && isColor));
  });
}
// 刷新歌词高亮色控件状态。
function updateLyricHighlightControls() {
  // 高亮色 input。
  var picker = document.getElementById('lyric-highlight-picker');
  // 高亮色显示文本。
  var value = document.getElementById('lyric-highlight-value');
  // 高亮自动按钮。
  var autoBtn = document.getElementById('lyric-highlight-auto-btn');
  // 当前高亮颜色。
  var color = normalizeHexColor(fx.lyricHighlightColor);
  if (picker) picker.value = color;
  if (value) value.textContent = fx.lyricHighlightMode === 'custom' ? color.toUpperCase() : '跟随歌词';
  if (autoBtn) autoBtn.classList.toggle('active', fx.lyricHighlightMode !== 'custom');
}
// 刷新歌词溢光颜色控件状态。
function updateLyricGlowControls() {
  // 溢光设置行。
  var row = document.getElementById('lyric-glow-row');
  // 溢光颜色 input。
  var picker = document.getElementById('lyric-glow-picker');
  // 溢光颜色显示文本。
  var value = document.getElementById('lyric-glow-value');
  // 溢光链接按钮。
  var linkBtn = document.getElementById('lyric-glow-link-btn');
  // 溢光颜色是否跟随高亮。
  var linked = fx.lyricGlowLinked !== false;
  // 当前溢光颜色。
  var color = normalizeHexColor(fx.lyricGlowColor || '#9db8cf');
  if (picker) picker.value = color;
  if (row) row.classList.toggle('linked', linked);
  if (value) value.textContent = linked ? '跟随高亮' : color.toUpperCase();
  if (linkBtn) {
    linkBtn.classList.toggle('active', linked);
    linkBtn.textContent = linked ? '链接' : '独立';
    linkBtn.title = linked ? '点击后单独设置溢光颜色' : '点击后让溢光跟随高亮';
  }
}
// 将视觉图标颜色写入 CSS 变量。
function applyIconAccentColors() {
  // 当前视觉图标颜色。
  var visualColor = normalizeHexColor(fx.visualIconColor || fxDefaults.visualIconColor || '#7fd8ff', '#7fd8ff');
  // 图标颜色 RGB。
  var visualRgb = hexToRgb(visualColor);
  // 文档根节点。
  var root = document.documentElement;
  root.style.setProperty('--visual-icon-color', visualColor);
  root.style.setProperty('--visual-icon-rgb', visualRgb.r + ',' + visualRgb.g + ',' + visualRgb.b);
}
// 刷新视觉图标颜色控件。
function updateIconAccentControls() {
  applyIconAccentColors();
  // 当前视觉图标颜色。
  var visualColor = normalizeHexColor(fx.visualIconColor || fxDefaults.visualIconColor || '#7fd8ff', '#7fd8ff');
  // 视觉图标颜色选择器。
  var visualPicker = document.getElementById('visual-icon-picker');
  // 视觉图标颜色文本。
  var visualValue = document.getElementById('visual-icon-value');
  if (visualPicker) visualPicker.value = visualColor;
  if (visualValue) visualValue.textContent = visualColor.toUpperCase();
}
// 设置视觉图标颜色。
function setVisualIconColor(color, silent) {
  fx.visualIconColor = normalizeHexColor(color || fxDefaults.visualIconColor || '#7fd8ff', '#7fd8ff');
  updateIconAccentControls();
  saveLyricLayout();
  if (!silent) showToast('视觉图标: ' + fx.visualIconColor.toUpperCase());
}
// 重置视觉图标颜色为默认值。
function resetVisualIconColor() {
  setVisualIconColor(fxDefaults.visualIconColor || '#7fd8ff');
}
// 应用自定义背景颜色、图片或视频。
function applyCustomBackground() {
  // 背景纯色。
  var color = normalizeHexColor(fx.backgroundColor || '#000000', '#000000');
  // 归一化后的背景媒体。
  var media = normalizeCustomBackgroundMedia(fx.backgroundMedia || fx.backgroundImage);
  // 背景图片地址。
  var image = media && media.type === 'image' ? media.src : '';
  // 是否为背景视频。
  var hasVideo = !!(media && media.type === 'video');
  // 背景媒体透明度。
  var opacity = clampRange(fx.backgroundOpacity == null ? 1 : Number(fx.backgroundOpacity), 0, 1);
  // 是否启用自定义颜色。
  var customColor = fx.backgroundColorMode === 'custom' || !!fx.backgroundColorCustom;
  // 是否需要覆盖默认封面背景。
  var override = !!media || customColor || opacity < 1;
  // 文档根节点。
  var root = document.documentElement;
  // 自定义背景图层。
  var layer = document.getElementById('custom-bg');
  // 自定义背景视频节点。
  var video = document.getElementById('custom-bg-video');
  root.style.setProperty('--custom-bg-color', color);
  document.body.classList.toggle('custom-background-override', override);
  document.body.classList.toggle('custom-background-flat', override && !media);
  document.body.classList.toggle('custom-background-video', hasVideo);
  if (layer) {
    // 背景图层的 CSS 变量。
    layer.style.setProperty('--custom-bg-image', image ? 'url("' + cssImageUrl(image) + '")' : 'none');
    layer.style.setProperty('--custom-bg-image-opacity', image ? opacity.toFixed(3) : '0');
    layer.style.setProperty('--custom-bg-video-opacity', hasVideo ? opacity.toFixed(3) : '0');
    layer.style.setProperty('--custom-bg-overlay-opacity', media ? '0.18' : '0');
  }
  // 背景视频应用 token，防止异步 blob 结果串写。
  var token = ++customBgApplyToken;
  if (!video) return;
  if (!hasVideo) {
    // 没有视频时停止并清理 video 节点。
    video.pause();
    video.removeAttribute('src');
    video.load();
    if (customBgObjectUrl) { URL.revokeObjectURL(customBgObjectUrl); customBgObjectUrl = ''; }
    return;
  }
  // 设置背景视频 src 并尝试播放。
  function setVideoSrc(src) {
    if (token !== customBgApplyToken || !src) return;
    // 如果旧 objectURL 不再使用则释放。
    if (customBgObjectUrl && customBgObjectUrl !== src) { URL.revokeObjectURL(customBgObjectUrl); customBgObjectUrl = ''; }
    if (video.getAttribute('src') !== src) {
      video.setAttribute('src', src);
      video.load();
    }
    video.muted = true;
    video.loop = true;
    video.playsInline = true;
    var p = video.play();
    if (p && p.catch) p.catch(function(){});
  }
  if (media.src) {
    // dataURL 或普通 URL 视频直接应用。
    setVideoSrc(media.src);
  } else if (media.id) {
    // IndexedDB 中的视频 blob 需要异步取出并转为 objectURL。
    getCustomBackgroundBlob(media.id).then(function(blob){
      if (token !== customBgApplyToken || !blob) return;
      if (customBgObjectUrl) URL.revokeObjectURL(customBgObjectUrl);
      customBgObjectUrl = URL.createObjectURL(blob);
      setVideoSrc(customBgObjectUrl);
    }).catch(function(err){ console.warn('background video load failed:', err); });
  }
}
// 刷新自定义背景相关控件。
function updateCustomBackgroundControls() {
  applyCustomBackground();
  // 当前背景颜色。
  var color = normalizeHexColor(fx.backgroundColor || '#000000', '#000000');
  // 背景颜色选择器。
  var picker = document.getElementById('bg-color-picker');
  // 背景颜色文本。
  var value = document.getElementById('bg-color-value');
  // 背景媒体文本。
  var imageValue = document.getElementById('bg-image-value');
  // 是否处于自定义颜色模式。
  var customColor = fx.backgroundColorMode === 'custom' || !!fx.backgroundColorCustom;
  if (picker) picker.value = color;
  if (value) value.textContent = customColor ? color.toUpperCase() : '\u5c01\u9762\u6e10\u53d8';
  if (picker && picker.closest) {
    // 给控件行打上封面模式状态。
    var row = picker.closest('.lyric-color-row');
    if (row) row.classList.toggle('bg-cover-mode', !customColor);
  }
  setRange('fx-bgopacity', fx.backgroundOpacity == null ? 1 : fx.backgroundOpacity);
  if (imageValue) imageValue.textContent = customBackgroundMediaLabel(fx.backgroundMedia || fx.backgroundImage);
  applyBackgroundMediaHint();
}
// 设置自定义背景颜色。
function setCustomBackgroundColor(color, silent, customFlag) {
  fx.backgroundColor = normalizeHexColor(color || '#000000', '#000000');
  fx.backgroundColorMode = customFlag === false ? 'cover' : 'custom';
  fx.backgroundColorCustom = customFlag !== false;
  updateCustomBackgroundControls();
  saveLyricLayout();
  if (!silent) showToast('背景颜色: ' + fx.backgroundColor.toUpperCase());
}
// 将背景颜色模式恢复为封面渐变。
function setCustomBackgroundCoverMode(silent) {
  fx.backgroundColorMode = 'cover';
  fx.backgroundColorCustom = false;
  fx.backgroundColor = normalizeHexColor(fx.backgroundColor || fxDefaults.backgroundColor || '#000000', '#000000');
  updateCustomBackgroundControls();
  saveLyricLayout();
  if (!silent) showToast('\u80cc\u666f\u989c\u8272: \u5c01\u9762\u6e10\u53d8');
}
// 重置自定义背景颜色。
function resetCustomBackgroundColor() {
  setCustomBackgroundCoverMode(false);
}
// 设置自定义背景透明度。
function setCustomBackgroundOpacity(value, silent) {
  fx.backgroundOpacity = clampRange(Number(value), 0, 1);
  fx.backgroundColorMode = 'custom';
  fx.backgroundColorCustom = true;
  updateCustomBackgroundControls();
  saveLyricLayout();
  if (!silent) showToast('背景透明度: ' + Math.round(fx.backgroundOpacity * 100) + '%');
}
// 设置自定义背景图片。
function setCustomBackgroundImage(src, silent) {
  // 归一化后的图片地址。
  var image = normalizeCustomBackgroundImage(src);
  fx.backgroundImage = image;
  fx.backgroundMedia = image ? { type: 'image', src: image } : null;
  updateCustomBackgroundControls();
  saveLyricLayout();
  if (!silent) showToast(fx.backgroundImage ? '背景图片已应用' : '背景图片已清除');
}
// 清除自定义背景图片。
function clearCustomBackgroundImage() {
  setCustomBackgroundImage('');
}
// 设置自定义背景媒体，兼容图片和视频。
function setCustomBackgroundMedia(media, silent) {
  media = normalizeCustomBackgroundMedia(media);
  fx.backgroundMedia = media;
  fx.backgroundImage = media && media.type === 'image' ? media.src : '';
  updateCustomBackgroundControls();
  saveLyricLayout();
  if (!silent) showToast(media ? (media.type === 'video' ? '背景视频已应用' : '背景图片已应用') : '背景媒体已清除');
}
// 读取本地图片文件并压缩为背景图片 dataURL。
function readBackgroundImageFile(file) {
  if (!file || !/^image\//i.test(file.type || '')) {
    showToast('请选择图片文件');
    return;
  }
  // 图片文件读取器。
  var reader = new FileReader();
  reader.onload = function(e) {
    // 临时图片对象，用于解码和缩放。
    var img = new Image();
    img.onload = function() {
      // 背景图最长边限制。
      var maxSide = 2200;
      // 原图宽度。
      var iw = img.naturalWidth || img.width || 1;
      // 原图高度。
      var ih = img.naturalHeight || img.height || 1;
      // 缩放比例。
      var scale = Math.min(1, maxSide / Math.max(iw, ih));
      // 输出宽度。
      var w = Math.max(1, Math.round(iw * scale));
      // 输出高度。
      var h = Math.max(1, Math.round(ih * scale));
      // 输出 canvas。
      var cv = document.createElement('canvas');
      cv.width = w; cv.height = h;
      // 输出绘制上下文。
      var cx = cv.getContext('2d');
      cx.drawImage(img, 0, 0, w, h);
      // 优先导出 webp。
      var out = '';
      try { out = cv.toDataURL('image/webp', 0.84); } catch (err) {}
      if (!/^data:image\/webp/i.test(out)) {
        // 不支持 webp 时降级为 jpeg，最后兜底原始 dataURL。
        try { out = cv.toDataURL('image/jpeg', 0.86); } catch (err2) { out = String(e.target.result || ''); }
      }
      setCustomBackgroundImage(out);
    };
    img.onerror = function(){ showToast('背景图片读取失败'); };
    img.src = e.target.result;
  };
  reader.onerror = function(){ showToast('背景图片读取失败'); };
  reader.readAsDataURL(file);
}
// 读取本地视频文件并保存为背景视频。
function readBackgroundVideoFile(file) {
  if (!file || !/^video\//i.test(file.type || '')) {
    showToast('请选择视频文件');
    return;
  }
  // 背景视频 blob 存储 id。
  var id = 'bg-video-' + Date.now() + '-' + Math.random().toString(16).slice(2);
  putCustomBackgroundBlob(id, file, { name: file.name || '', mime: file.type || '', size: file.size || 0 }).then(function(){
    setCustomBackgroundMedia({ type: 'video', id: id, name: file.name || '', mime: file.type || '', size: file.size || 0 });
  }).catch(function(err){
    console.warn('background video store failed:', err);
    if ((file.size || 0) > 18 * 1024 * 1024) {
      // 大视频不再转 dataURL，避免本地存储和内存压力过大。
      showToast('视频较大，当前环境无法保存，请换小一点的视频');
      return;
    }
    // IndexedDB 失败时，小视频降级为 dataURL。
    var reader = new FileReader();
    reader.onload = function(e){
      setCustomBackgroundMedia({ type: 'video', src: String(e.target.result || ''), name: file.name || '', mime: file.type || '', size: file.size || 0 });
    };
    reader.onerror = function(){ showToast('背景视频读取失败'); };
    reader.readAsDataURL(file);
  });
}
// 根据文件类型读取自定义背景媒体。
function readBackgroundMediaFile(file) {
  if (!file) return;
  if (/^image\//i.test(file.type || '')) readBackgroundImageFile(file);
  else if (/^video\//i.test(file.type || '')) readBackgroundVideoFile(file);
  else showToast('请选择图片或视频文件');
}
// 将 UI 强调色写入 CSS 变量。
function applyUiAccentColor() {
  // 当前 UI 强调色。
  var color = normalizeHexColor(fx.uiAccentColor || '#00f5d4', '#00f5d4');
  // 强调色 RGB。
  var rgb = hexToRgb(color);
  // 文档根节点。
  var root = document.documentElement;
  root.style.setProperty('--fc-accent', color);
  root.style.setProperty('--fc-accent-hov', color);
  root.style.setProperty('--fc-accent-rgb', rgb.r + ',' + rgb.g + ',' + rgb.b);
  root.style.setProperty('--glass-border', 'rgba(' + rgb.r + ',' + rgb.g + ',' + rgb.b + ',.30)');
  root.style.setProperty('--glass-shadow-focus', '0 24px 72px rgba(0,0,0,.34),0 0 0 1px rgba(' + rgb.r + ',' + rgb.g + ',' + rgb.b + ',.13),0 0 42px rgba(' + rgb.r + ',' + rgb.g + ',' + rgb.b + ',.075),inset 0 1px 0 rgba(255,255,255,.20)');
}
// 刷新 UI 强调色控件。
function updateUiAccentControls() {
  applyUiAccentColor();
  // 当前 UI 强调色。
  var color = normalizeHexColor(fx.uiAccentColor || '#00f5d4', '#00f5d4');
  // UI 强调色选择器。
  var picker = document.getElementById('ui-accent-picker');
  // UI 强调色文本。
  var value = document.getElementById('ui-accent-value');
  if (picker) picker.value = color;
  if (value) value.textContent = color.toUpperCase();
}
// 设置 UI 强调色。
function setUiAccentColor(color, silent) {
  fx.uiAccentColor = normalizeHexColor(color || '#00f5d4', '#00f5d4');
  updateUiAccentControls();
  if (shelfManager && shelfManager.refreshTheme) shelfManager.refreshTheme();
  saveLyricLayout();
  if (!silent) showToast('界面高亮: ' + fx.uiAccentColor.toUpperCase());
}
// 重置 UI 强调色。
function resetUiAccentColor() {
  setUiAccentColor(fxDefaults.uiAccentColor || '#00f5d4');
}
// 刷新视觉主色控件。
function updateVisualTintControls() {
  // 视觉主色选择器。
  var picker = document.getElementById('visual-tint-picker');
  // 视觉主色文本。
  var value = document.getElementById('visual-tint-value');
  // 自动取色按钮。
  var autoBtn = document.getElementById('visual-tint-auto-btn');
  // 当前视觉主色。
  var color = normalizeHexColor(fx.visualTintColor || '#9db8cf');
  document.documentElement.style.setProperty('--visual-tint', color);
  if (picker) picker.value = color;
  if (value) value.textContent = fx.visualTintMode === 'custom' ? color.toUpperCase() : '封面取色';
  if (autoBtn) autoBtn.classList.toggle('active', fx.visualTintMode !== 'custom');
}
// 设置视觉主色为封面自动取色。
function setVisualTintAuto() {
  fx.visualTintMode = 'auto';
  updateVisualTintControls();
  syncFxUniforms();
  saveLyricLayout();
  showToast('视觉主色: 封面取色');
}
// 重置视觉主色为默认自动模式。
function resetVisualTintColor() {
  fx.visualTintMode = 'auto';
  fx.visualTintColor = normalizeHexColor(fxDefaults.visualTintColor || '#9db8cf');
  updateVisualTintControls();
  syncFxUniforms();
  saveLyricLayout();
  showToast('视觉主色已恢复默认');
}
// 设置自定义视觉主色。
function setVisualTintCustom(color, silent) {
  fx.visualTintMode = 'custom';
  fx.visualTintColor = normalizeHexColor(color || '#9db8cf');
  updateVisualTintControls();
  syncFxUniforms();
  saveLyricLayout();
  if (!silent) showToast('视觉主色: ' + fx.visualTintColor.toUpperCase());
}
// 封面取色器状态。
var coverColorPickerState = { target: 'visualTint', canvas: null };
// 获取当前可用于取色的封面 canvas。
function currentCoverPickerCanvas() {
  if (coverPickerCanvas && coverPickerCanvas.getContext) return coverPickerCanvas;
  if (coverTex && coverTex.image && coverTex.image.getContext) return coverTex.image;
  return null;
}
// 生成封面取色器推荐色块。
function coverPickerSwatchColors() {
  // 当前舞台歌词色板。
  var pal = stageLyrics.coverPalette || stageLyrics.palette || {};
  // 候选颜色列表。
  var list = [pal.primary, pal.secondary, pal.highlight, fx.visualTintColor, fx.uiAccentColor]
    .map(function(c){ return normalizeHexColor(c || '', ''); })
    .filter(function(c){ return /^#[0-9a-f]{6}$/i.test(c); });
  // 去重表。
  var seen = {};
  return list.filter(function(c){
    if (seen[c]) return false;
    seen[c] = true;
    return true;
  }).slice(0, 5);
}
// 设置封面取色器预览颜色。
function setCoverPickerPreview(hex) {
  // 取色预览节点。
  var preview = document.getElementById('cover-color-preview');
  if (preview) preview.style.setProperty('--picked', normalizeHexColor(hex || '#9db8cf'));
}
// 渲染封面取色器推荐色块。
function renderCoverPickerSwatches() {
  // 推荐色块容器。
  var wrap = document.getElementById('cover-color-swatches');
  if (!wrap) return;
  // 推荐颜色列表。
  var colors = coverPickerSwatchColors();
  wrap.innerHTML = colors.map(function(c){
    return '<button type="button" style="--c:' + c + '" title="' + c.toUpperCase() + '" onclick="applyCoverPickerColor(\'' + c + '\')"></button>';
  }).join('');
}
// 打开封面取色器。
function openCoverColorPicker(target) {
  // 目标颜色字段。
  target = target || 'visualTint';
  // 取色器弹层。
  var pop = document.getElementById('cover-color-pop');
  // 封面预览区域。
  var art = document.getElementById('cover-color-art');
  // 提示文本节点。
  var hint = document.getElementById('cover-color-hint');
  if (pop && pop.classList.contains('show') && coverColorPickerState.target === target) {
    closeCoverColorPicker();
    return;
  }
  // 当前可取色封面 canvas。
  var cv = currentCoverPickerCanvas();
  coverColorPickerState.target = target;
  coverColorPickerState.canvas = cv;
  if (!pop || !art) return;
  if (!cv) {
    // 没有封面 canvas 时回退自动取色。
    setVisualTintAuto();
    closeCoverColorPicker();
    showToast('暂无封面，已切换为自动封面取色');
    return;
  }
  // 封面预览图片地址。
  var imgSrc = '';
  try { imgSrc = cv.toDataURL('image/jpeg', 0.84); } catch (e) {}
  if (!imgSrc && currentCoverSource && currentCoverSource.src) imgSrc = currentCoverSource.src;
  art.style.backgroundImage = imgSrc ? 'url("' + cssImageUrl(imgSrc) + '")' : '';
  setCoverPickerPreview(fx.visualTintColor || (stageLyrics.coverPalette && stageLyrics.coverPalette.primary) || '#9db8cf');
  renderCoverPickerSwatches();
  if (hint) hint.textContent = '点击专辑封面任意位置取色，或使用下方推荐色。';
  pop.classList.add('show');
  placeFxFloatingPanel(pop, document.getElementById('visual-tint-auto-btn') || document.getElementById('visual-tint-picker') || art, { gap: 12, pad: 14 });
}
// 关闭封面取色器。
function closeCoverColorPicker() {
  // 取色器弹层。
  var pop = document.getElementById('cover-color-pop');
  if (pop) pop.classList.remove('show');
  hideCoverColorLoupe();
}
// 应用封面取色器选择的颜色。
function applyCoverPickerColor(hex) {
  hex = normalizeHexColor(hex || '#9db8cf');
  setCoverPickerPreview(hex);
  if (coverColorPickerState.target === 'visualTint') {
    // 当前只将取色结果应用到视觉主色。
    setVisualTintCustom(hex, true);
    showToast('视觉主色: ' + hex.toUpperCase());
  }
  closeCoverColorPicker();
}
// 移动封面取色放大镜。
function moveCoverColorLoupe(e) {
  // 当前取色 canvas。
  var cv = coverColorPickerState.canvas || currentCoverPickerCanvas();
  // 放大镜节点。
  var loupe = document.getElementById('cover-color-loupe');
  // 封面预览节点。
  var art = document.getElementById('cover-color-art');
  if (!cv || !loupe || !art) return;
  // 封面预览区域尺寸。
  var rect = art.getBoundingClientRect();
  // 归一化 X。
  var x = clampRange((e.clientX - rect.left) / Math.max(1, rect.width), 0, 1);
  // 归一化 Y。
  var y = clampRange((e.clientY - rect.top) / Math.max(1, rect.height), 0, 1);
  // 放大镜背景图。
  var imgSrc = '';
  try { imgSrc = cv.toDataURL('image/jpeg', 0.84); } catch (err) {}
  if (imgSrc) {
    loupe.style.backgroundImage = 'url("' + cssImageUrl(imgSrc) + '")';
    loupe.style.backgroundSize = '680% 680%';
    loupe.style.backgroundPosition = (x * 100).toFixed(2) + '% ' + (y * 100).toFixed(2) + '%';
  }
  loupe.style.left = Math.min(window.innerWidth - 128, e.clientX + 18) + 'px';
  loupe.style.top = Math.min(window.innerHeight - 128, e.clientY + 18) + 'px';
  loupe.classList.add('show');
}
// 隐藏封面取色放大镜。
function hideCoverColorLoupe() {
  var loupe = document.getElementById('cover-color-loupe');
  if (loupe) loupe.classList.remove('show');
}
// 从封面预览点击位置读取像素颜色。
function pickCoverColorFromArt(e) {
  // 当前取色 canvas。
  var cv = coverColorPickerState.canvas || currentCoverPickerCanvas();
  if (!cv || !cv.getContext) return;
  // 点击目标区域。
  var rect = e.currentTarget.getBoundingClientRect();
  // 点击归一化 X。
  var x = clampRange((e.clientX - rect.left) / Math.max(1, rect.width), 0, 1);
  // 点击归一化 Y。
  var y = clampRange((e.clientY - rect.top) / Math.max(1, rect.height), 0, 1);
  // canvas 像素 X。
  var sx = Math.max(0, Math.min(cv.width - 1, Math.floor(x * cv.width)));
  // canvas 像素 Y。
  var sy = Math.max(0, Math.min(cv.height - 1, Math.floor(y * cv.height)));
  try {
    // 读取单像素 RGB。
    var data = cv.getContext('2d').getImageData(sx, sy, 1, 1).data;
    applyCoverPickerColor(rgbToHexColor(data[0], data[1], data[2]));
  } catch (err) {
    showToast('封面取色不可用，已保留自动取色');
    setVisualTintAuto();
    closeCoverColorPicker();
  }
}
// 刷新歌词字体按钮状态。
function updateLyricFontControls() {
  document.querySelectorAll('#lyric-font-grid button').forEach(function(btn){
    btn.classList.toggle('active', btn.dataset.font === normalizeLyricFontKey(fx.lyricFont));
  });
}
// 设置歌词字体。
function setLyricFont(key) {
  fx.lyricFont = normalizeLyricFontKey(key);
  updateLyricFontControls();
  refreshCurrentLyricStyle();
  saveLyricLayout();
  showToast('歌词字体已切换');
}
// 设置歌词溢光是否跟随高亮色。
function setLyricGlowLinked(linked, openPicker) {
  fx.lyricGlowLinked = linked !== false;
  if (!fx.lyricGlowLinked) fx.lyricGlowColor = normalizeHexColor(fx.lyricGlowColor || fx.lyricHighlightColor || '#9db8cf');
  setStageLyricPalette(fx.lyricColorMode === 'custom' ? lyricPaletteFromHex(fx.lyricColor) : (stageLyrics.coverPalette || stageLyrics.palette));
  updateLyricGlowControls();
  saveLyricLayout();
  if (openPicker) {
    // 解除链接后自动打开颜色选择器。
    setTimeout(function(){
      var picker = document.getElementById('lyric-glow-picker');
      if (picker) picker.click();
    }, 0);
  }
}
// 切换歌词溢光链接状态。
function toggleLyricGlowLink(e) {
  if (e && e.stopPropagation) e.stopPropagation();
  setLyricGlowLinked(fx.lyricGlowLinked === false);
}
// 点击溢光设置行时，如果仍跟随高亮则切换到独立颜色。
function handleLyricGlowRowClick(e) {
  if (fx.lyricGlowLinked !== false) {
    if (e && e.preventDefault) e.preventDefault();
    setLyricGlowLinked(false, true);
  }
}
// 设置自定义歌词溢光颜色。
function setLyricGlowCustom(color, silent) {
  fx.lyricGlowLinked = false;
  fx.lyricGlowColor = normalizeHexColor(color || '#9db8cf');
  setStageLyricPalette(fx.lyricColorMode === 'custom' ? lyricPaletteFromHex(fx.lyricColor) : (stageLyrics.coverPalette || stageLyrics.palette));
  updateLyricGlowControls();
  saveLyricLayout();
  if (!silent) showToast('溢光颜色: ' + fx.lyricGlowColor.toUpperCase());
}
// 设置歌词主色为封面自动取色。
function setLyricColorAuto() {
  fx.lyricColorMode = 'auto';
  setStageLyricPalette(stageLyrics.coverPalette || stageLyrics.palette);
  updateLyricColorControls();
  updateLyricHighlightControls();
  updateLyricGlowControls();
  saveLyricLayout();
  showToast('歌词颜色: 封面取色');
}
// 设置自定义歌词主色。
function setLyricColorCustom(color, silent) {
  fx.lyricColorMode = 'custom';
  fx.lyricColor = normalizeHexColor(color);
  setStageLyricPalette(lyricPaletteFromHex(fx.lyricColor));
  updateLyricColorControls();
  updateLyricHighlightControls();
  updateLyricGlowControls();
  saveLyricLayout();
  if (!silent) showToast('歌词颜色: ' + fx.lyricColor.toUpperCase());
}
// 从预设色板中选择歌词主色。
function setLyricColorPreset(i) {
  // 目标预设色。
  var p = lyricColorPresets[i];
  if (!p) return;
  setLyricColorCustom(p.color);
}
// 设置歌词高亮色为跟随歌词。
function setLyricHighlightAuto() {
  fx.lyricHighlightMode = 'auto';
  setStageLyricPalette(fx.lyricColorMode === 'custom' ? lyricPaletteFromHex(fx.lyricColor) : (stageLyrics.coverPalette || stageLyrics.palette));
  updateLyricHighlightControls();
  updateLyricGlowControls();
  saveLyricLayout();
  showToast('高亮颜色: 跟随歌词');
}
// 设置自定义歌词高亮色。
function setLyricHighlightCustom(color, silent) {
  fx.lyricHighlightMode = 'custom';
  fx.lyricHighlightColor = normalizeHexColor(color);
  setStageLyricPalette(fx.lyricColorMode === 'custom' ? lyricPaletteFromHex(fx.lyricColor) : (stageLyrics.coverPalette || stageLyrics.palette));
  updateLyricHighlightControls();
  updateLyricGlowControls();
  saveLyricLayout();
  if (!silent) showToast('高亮颜色: ' + fx.lyricHighlightColor.toUpperCase());
}

// 构建视觉预设卡片网格。
function buildPresetGrid() {
  // 预设网格容器。
  var grid = document.getElementById('preset-grid');
  if (!grid) return;
  // 去重表。
  var seen = {};
  // 展示顺序，先使用指定顺序。
  var order = presetDisplayOrder.filter(function(id){
    // 当前预设 id 是否合法且未出现。
    var ok = id >= 0 && id < presetMeta.length && !seen[id];
    seen[id] = true;
    return ok;
  });
  presetMeta.forEach(function(_, id){
    // 把未列入 presetDisplayOrder 的预设追加到末尾。
    if (!seen[id]) order.push(id);
  });
  grid.innerHTML = order.map(function(i){
    // 预设元信息。
    var p = presetMeta[i];
    // 预设描述支持 HTML 覆盖。
    var desc = p.descHtml || p.desc;
    return '<div class="preset-card" data-preset="' + i + '" onclick="setPreset(' + i + ')">' +
      '<div class="pc-icon">' + presetIcons[i] + '</div>' +
      '<div class="pc-name">' + p.name + '</div>' +
      '<div class="pc-desc">' + desc + '</div>' +
    '</div>';
  }).join('');
  refreshPresetGrid();
}
// 刷新视觉预设卡片选中态。
function refreshPresetGrid() {
  document.querySelectorAll('.preset-card').forEach(function(el){
    el.classList.toggle('active', Number(el.dataset.preset) === fx.preset);
  });
}
// 启动预设切换时的粒子过渡效果。
function triggerPresetParticleTransition(fromPreset, toPreset) {
  presetTransition.active = true;
  presetTransition.start = uniforms.uTime.value;
  presetTransition.duration = toPreset === 5 ? 0.30 : 0.24;
  presetTransition.from = fromPreset;
  presetTransition.to = toPreset;
  // 新视觉预设包含唱片、星河和骷髅等。
  var newVisual = toPreset >= 4;
  // 星河壁纸预设需要更轻的扰动。
  var wallpaperFlow = toPreset === 5;
  uniforms.uScatter.value = Math.max(uniforms.uScatter.value, fx.scatter + (newVisual ? (wallpaperFlow ? 0.008 : 0.024) : 0.12));
  uniforms.uBurstAmt.value = Math.max(uniforms.uBurstAmt.value, wallpaperFlow ? 0.05 : 0.15);
  camPunch = Math.max(camPunch, wallpaperFlow ? 0.04 : 0.12);
  for (var i = 0; i < 3; i++) {
    // 预设切换时触发几圈涟漪，掩盖几何重排。
    triggerRipple((Math.random() - 0.5) * 3.4, (Math.random() - 0.5) * 3.4, 0.58 + Math.random() * 0.32);
  }
  // 目标预设卡片。
  var card = document.querySelector('.preset-card[data-preset="' + toPreset + '"]');
  if (card) {
    card.classList.remove('switching');
    void card.offsetWidth;
    card.classList.add('switching');
    setTimeout(function(){ card.classList.remove('switching'); }, 760);
  }
}
// 每帧推进预设切换过渡。
function tickPresetTransition() {
  if (!presetTransition.active) return;
  // 原始过渡进度。
  var raw = (uniforms.uTime.value - presetTransition.start) / presetTransition.duration;
  // 夹紧后的过渡进度。
  var t = Math.max(0, Math.min(1, raw));
  // 半正弦波用于中段增强。
  var wave = Math.sin(t * Math.PI);
  // 是否切到新视觉预设。
  var newVisual = presetTransition.to >= 4;
  // 是否切到星河壁纸预设。
  var wallpaperFlow = presetTransition.to === 5;
  uniforms.uScatter.value = Math.max(uniforms.uScatter.value, fx.scatter + wave * (newVisual ? (wallpaperFlow ? 0.008 : 0.026) : 0.16));
  uniforms.uBurstAmt.value = Math.max(uniforms.uBurstAmt.value, wave * (wallpaperFlow ? 0.045 : (newVisual ? 0.12 : 0.15)));
  uniforms.uPointScale.value = fx.point * (1 + wave * (wallpaperFlow ? 0.016 : 0.048));
  if (raw >= 1) {
    presetTransition.active = false;
    syncFxUniforms();
  }
}
// 切换视觉预设。
function setPreset(p, opts) {
  opts = opts || {};
  // 目标预设索引。
  p = Math.max(0, Math.min(presetMeta.length - 1, normalizeVisualPresetIndex(p, DEFAULT_PLAYBACK_VISUAL_PRESET)));
  // 上一个预设索引。
  var prev = fx.preset;
  // 是否真的发生变化。
  var changed = prev !== p;
  fx.preset = p;
  if (changed && prev === SKULL_PRESET_INDEX && p !== SKULL_PRESET_INDEX) clearSkullPresetResidue();
  if (p === SKULL_PRESET_INDEX) loadSkullParticleAsset();
  uniforms.uPreset.value = p;
  refreshPresetGrid();
  if (changed && !opts.skipTransition) triggerPresetParticleTransition(prev, p);
  // 每个预设对应的相机基线 (改 userOrbit)
  if (changed && !opts.preserveCamera) {
    // 预设切换时重置轨道相机默认基线。
    if (p === 1)      { orbit.userRadius = 6.2; orbit.userPhi = 0.03; orbit.userTheta = 0.0; orbit.baselineRadius = 6.2; orbit.baselinePhi = 0.03; }
    else if (p === 2) { orbit.userRadius = 7.0; orbit.userPhi = 0.15; orbit.userTheta = 0.0; orbit.baselineRadius = 7.0; orbit.baselinePhi = 0.15; }
    else if (p === 3) { orbit.userRadius = 8.0; orbit.userPhi = 0.05; orbit.userTheta = 0.0; orbit.baselineRadius = 8.0; orbit.baselinePhi = 0.05; }
    else if (p === 4) { orbit.userRadius = 6.5; orbit.userPhi = 0.04; orbit.userTheta = 0.0; orbit.baselineRadius = 6.5; orbit.baselinePhi = 0.04; }
    else if (p === 5) { orbit.userRadius = 9.4; orbit.userPhi = 0.34; orbit.userTheta = -0.52; orbit.baselineRadius = 9.4; orbit.baselinePhi = 0.34; }
    else if (p === 6) { orbit.userRadius = 7.4; orbit.userPhi = 0.10; orbit.userTheta = 0.18; orbit.baselineRadius = 7.4; orbit.baselinePhi = 0.10; }
    else              { orbit.userRadius = 6.6; orbit.userPhi = 0.08; orbit.userTheta = 0.0; orbit.baselineRadius = 6.6; orbit.baselinePhi = 0.08; }
    orbit.baselineTheta = p === 5 ? -0.52 : (p === 6 ? 0.18 : 0.0);
  }
  if (changed && !opts.silent) showToast('视觉预设: ' + presetMeta[p].name);
  // 是否把本次预设写入播放期默认预设。
  var shouldCommitPlaybackPreset = !!opts.commitPlaybackPreset || !opts.noSave;
  if (shouldCommitPlaybackPreset) {
    playbackVisualPreset = p;
  }
  if (!opts.noSave) {
    saveLyricLayout();
  }
}

// 将 fx 运行时配置同步到 shader uniforms 和可见对象。
function syncFxUniforms() {
  uniforms.uPreset.value = fx.preset;
  uniforms.uIntensity.value = fx.intensity;
  uniforms.uDepth.value = fx.depth;
  uniforms.uPointScale.value = fx.point;
  uniforms.uSpeed.value = fx.speed;
  uniforms.uTwist.value = fx.twist;
  uniforms.uColorBoost.value = fx.color;
  uniforms.uScatter.value = fx.scatter;
  uniforms.uCoverRes.value = normalizeCoverResolution(fx.coverResolution);
  uniforms.uBgFade.value = fx.bgFade;
  uniforms.uBloomStrength.value = fx.bloom ? fx.bloomStrength : 0;
  if (bloomParticles) bloomParticles.visible = fx.bloom && fx.bloomStrength > 0.01;
  uniforms.uEdgeEnabled.value = fx.edge ? 1 : 0;
  // 视觉自定义主色。
  if (uniforms.uTintColor) uniforms.uTintColor.value.set(normalizeHexColor(fx.visualTintColor || '#9db8cf'));
  // 只有自定义主色模式才提高色彩染色强度。
  if (uniforms.uTintStrength) uniforms.uTintStrength.value = fx.visualTintMode === 'custom' ? 0.42 : 0;
  syncSkullParticleColors();
}
// 设置范围输入控件的值和 output 文本。
function setRange(id, value) {
  // 范围输入节点。
  var el = document.getElementById(id);
  if (!el) return;
  // 特殊滑块值归一化。
  if (id === 'fx-lyricglow') value = Math.min(0.85, Math.max(0, value));
  if (id === 'fx-coverres') value = normalizeCoverResolution(value);
  if (id === 'fx-glassaberration') value = normalizeControlGlassChromaticOffset(value);
  el.value = value;
  // 当前滑块旁的输出文本。
  var out = el.parentElement.querySelector('output');
  if (out) out.textContent = id === 'fx-coverres'
    ? coverParticleCountLabel(value)
    : (id === 'fx-lyricweight' || id === 'fx-glassaberration' || id === 'fx-lyrictiltx' || id === 'fx-lyrictilty' || id === 'fx-shelfangle' ? String(Math.round(Number(value) || 0)) : Number(value).toFixed(id === 'fx-lyricspacing' ? 3 : 2));
}
// 刷新开发中锁定功能的控件状态。
function updateDevelopmentFxControls() {
  [
    ['wallpaperMode', 't-wallpaperMode', '开发中，暂不可用']
  ].forEach(function(item){
    // 当前功能是否被开发锁锁定。
    var locked = isDevelopmentLockedFx(item[0]);
    // 对应开关节点。
    var el = document.getElementById(item[1]);
    if (!el) return;
    el.classList.toggle('dev-locked', locked);
    if (locked) {
      el.classList.remove('on');
      el.setAttribute('aria-disabled', 'true');
      el.title = '开发中，暂不可用';
    } else {
      el.removeAttribute('aria-disabled');
      el.title = item[2];
    }
  });
  [
    ['wallpaperMode', 'fx-wallpaperopacity']
  ].forEach(function(item){
    // 当前功能是否被开发锁锁定。
    var locked = isDevelopmentLockedFx(item[0]);
    // 对应输入节点。
    var input = document.getElementById(item[1]);
    if (!input) return;
    input.disabled = locked;
    // 输入所在行。
    var row = input.closest && input.closest('.fx-slider');
    if (row) row.classList.toggle('dev-locked', locked);
  });
}
// 刷新后台策略和画质档位控件。
function updatePerformanceControls() {
  fx.performanceBackground = normalizePerformanceBackgroundMode(fx.performanceBackground, fx.liveBackgroundKeep === true);
  fx.liveBackgroundKeep = fx.performanceBackground === 'keep';
  fx.performanceQuality = normalizePerformanceQuality(fx.performanceQuality);
  // 后台策略分段按钮。
  document.querySelectorAll('#performance-background-seg [data-performance-background]').forEach(function(btn){
    btn.classList.toggle('active', btn.getAttribute('data-performance-background') === fx.performanceBackground);
  });
  // 画质档位分段按钮。
  document.querySelectorAll('#performance-quality-seg [data-performance-quality]').forEach(function(btn){
    btn.classList.toggle('active', btn.getAttribute('data-performance-quality') === fx.performanceQuality);
  });
  // 旧保持后台开关兼容。
  var liveBackgroundKeepToggle = document.getElementById('t-liveBackgroundKeep');
  if (liveBackgroundKeepToggle) liveBackgroundKeepToggle.classList.toggle('on', fx.liveBackgroundKeep === true);
}
// 设置后台运行策略。
function setPerformanceBackgroundMode(mode, silent) {
  // 归一化后的后台策略。
  var next = normalizePerformanceBackgroundMode(mode, false);
  fx.performanceBackground = next;
  fx.liveBackgroundKeep = next === 'keep';
  updatePerformanceControls();
  saveLyricLayout();
  updateRenderPowerClasses();
  applyRendererPowerMode();
  if (next === 'keep') recoverVisualsAfterBackground('performance-background-keep');
  else if (next === 'release' && isDeepBackgroundMode()) trimRuntimeCaches('performance-release', true);
  if (!silent) {
    showToast(next === 'keep' ? '后台策略: 保持运行' : (next === 'release' ? '后台策略: 停止并释放' : '后台策略: 自动优化'));
  }
}
// 设置渲染画质档位。
function setPerformanceQualityMode(mode, silent) {
  // 归一化后的画质档位。
  var next = normalizePerformanceQuality(mode);
  fx.performanceQuality = next;
  updatePerformanceControls();
  applyRendererPowerMode();
  saveLyricLayout();
  if (!silent) {
    // 档位展示标签。
    var label = next === 'eco' ? '低' : (next === 'balanced' ? '中' : (next === 'ultra' ? '超高' : '高'));
    showToast('画质档位: ' + label);
  }
}
// 将当前 fx 状态同步到所有控制台输入、开关和颜色控件。
function updateFxInputs() {
  normalizeDevelopmentLockedFxState();
  applyShelfCameraDefaultAngle(false);
  // 数值滑块。
  setRange('fx-intensity', fx.intensity);
  setRange('fx-cineshake', fx.cinemaShake);
  setRange('fx-depth', fx.depth);
  setRange('fx-coverres', fx.coverResolution);
  setRange('fx-lyricglow', fx.lyricGlowStrength);
  setRange('fx-bgopacity', fx.backgroundOpacity == null ? 1 : fx.backgroundOpacity);
  setRange('fx-glassaberration', fx.controlGlassChromaticOffset);
  setRange('fx-wallpaperopacity', fx.wallpaperOpacity);
  setRange('fx-shelfsize', fx.shelfSize);
  setRange('fx-shelfx', fx.shelfOffsetX);
  setRange('fx-shelfy', fx.shelfOffsetY);
  setRange('fx-shelfz', fx.shelfOffsetZ);
  setRange('fx-shelfangle', fx.shelfAngleY);
  setRange('fx-shelfopacity', fx.shelfOpacity);
  setRange('fx-shelfbgalpha', fx.shelfBgOpacity);
  setRange('fx-lyricspacing', fx.lyricLetterSpacing);
  setRange('fx-lyriclineheight', fx.lyricLineHeight);
  setRange('fx-lyricweight', fx.lyricWeight);
  setRange('fx-lyricscale', fx.lyricScale);
  setRange('fx-lyricx', fx.lyricOffsetX);
  setRange('fx-lyricy', fx.lyricOffsetY);
  setRange('fx-lyricz', fx.lyricOffsetZ);
  setRange('fx-lyrictiltx', fx.lyricTiltX);
  setRange('fx-lyrictilty', fx.lyricTiltY);
  setRange('fx-point', fx.point);
  setRange('fx-speed', fx.speed);
  setRange('fx-twist', fx.twist);
  setRange('fx-color', fx.color);
  setRange('fx-bloom', fx.bloomStrength);
  setRange('fx-scatter', fx.scatter);
  setRange('fx-bgfade', fx.bgFade);
  updateLyricGlowControls();
  // 同步开关
  // 浮空粒子开关。
  document.getElementById('t-float').classList.toggle('on', fx.floatLayer);
  var floatToggle = document.getElementById('t-float');
  if (floatToggle) floatToggle.classList.toggle('on', fx.floatLayer);
  // 电影化镜头开关。
  document.getElementById('t-cinema').classList.toggle('on', fx.cinema);
  // 歌词溢光开关。
  var lyricGlowToggle = document.getElementById('t-lyricGlow');
  if (lyricGlowToggle) lyricGlowToggle.classList.toggle('on', fx.lyricGlow);
  // 歌词溢光节拍开关。
  var lyricGlowBeatToggle = document.getElementById('t-lyricGlowBeat');
  if (lyricGlowBeatToggle) lyricGlowBeatToggle.classList.toggle('on', fx.lyricGlowBeat);
  // 歌词溢光粒子开关。
  var lyricGlowParticlesToggle = document.getElementById('t-lyricGlowParticles');
  if (lyricGlowParticlesToggle) lyricGlowParticlesToggle.classList.toggle('on', fx.lyricGlowParticles);
  // 歌词相机锁定开关。
  var lyricCameraLockToggle = document.getElementById('t-lyricCameraLock');
  if (lyricCameraLockToggle) lyricCameraLockToggle.classList.toggle('on', fx.lyricCameraLock);
  // Bloom 开关。
  document.getElementById('t-bloom').classList.toggle('on', fx.bloom);
  // 边缘深度开关。
  document.getElementById('t-edge').classList.toggle('on', fx.edge);
  // 壁纸模式开关。
  var wallpaperModeToggle = document.getElementById('t-wallpaperMode');
  if (wallpaperModeToggle) wallpaperModeToggle.classList.toggle('on', fx.wallpaperMode);
  // 后台保持运行兼容开关。
  var liveBackgroundKeepToggle = document.getElementById('t-liveBackgroundKeep');
  if (liveBackgroundKeepToggle) liveBackgroundKeepToggle.classList.toggle('on', fx.liveBackgroundKeep === true);
  updatePerformanceControls();
  updateDevelopmentFxControls();
  // AI 深度开关。
  var aiDepthToggle = document.getElementById('t-aidepth');
  if (aiDepthToggle) aiDepthToggle.classList.toggle('on', fx.aiDepth);
  // 三态
  // 歌单架模式分段按钮。
  document.querySelectorAll('#shelf-seg button').forEach(function(b){ b.classList.toggle('active', b.dataset.shelf === fx.shelf); });
  // 其它派生控件状态。
  updateShelfControlUi();
  refreshPresetGrid();
  updateLyricColorControls();
  updateLyricHighlightControls();
  updateLyricGlowControls();
  updateLyricFontControls();
  updateUiAccentControls();
  updateIconAccentControls();
  updateCustomBackgroundControls();
  updateVisualTintControls();
  applyControlGlassChromaticOffset();
  syncFxUniforms();
}
// 播放单个滑块重置按钮动画。
function animateFxResetButton(btn) {
  if (!btn || !window.gsap) return;
  window.gsap.fromTo(btn, { rotate: -120, scale: 0.88 }, { rotate: 0, scale: 1, duration: 0.48, ease: 'expo.out', overwrite: true });
  window.gsap.fromTo(btn, { boxShadow: '0 0 0 0 rgba(244,210,138,.38)' }, { boxShadow: '0 0 0 8px rgba(244,210,138,0)', duration: 0.55, ease: 'sine.out', overwrite: true });
}
// 将指定滑块恢复到默认值。
function resetFxSliderValue(id, key, btn) {
  if (!Object.prototype.hasOwnProperty.call(fxDefaults, key)) return;
  if (key === 'shelfAngleY') {
    // 歌单架角度恢复为当前相机模式默认值。
    fx.shelfAngleYManual = false;
    fx.shelfAngleY = shelfDefaultAngleForCameraMode(fx.shelfCameraMode);
  } else {
    fx[key] = fxDefaults[key];
  }
  setRange(id, fx[key]);
  if (key === 'coverResolution') applyCoverParticleResolution(fx[key], { reload: true });
  if (key === 'controlGlassChromaticOffset') applyControlGlassChromaticOffset();
  syncFxUniforms();
  if (key === 'lyricLetterSpacing' || key === 'lyricLineHeight' || key === 'lyricWeight') refreshCurrentLyricStyle();
  saveLyricLayout();
  animateFxResetButton(btn);
  showToast('已恢复默认数值');
}
// 给指定滑块补充单项重置按钮。
function ensureFxSliderResetButton(id, key) {
  // 目标滑块。
  var el = document.getElementById(id);
  if (!el || !el.parentElement || el.parentElement.querySelector('.fx-reset-one')) return;
  // 重置按钮。
  var btn = document.createElement('button');
  btn.type = 'button';
  btn.className = 'fx-reset-one';
  btn.title = '恢复当前滑条默认值';
  btn.setAttribute('aria-label', '恢复当前滑条默认值');
  btn.innerHTML = '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round" stroke-linejoin="round"><path d="M3 12a9 9 0 1 0 3-6.7"/><path d="M3 4v5h5"/></svg>';
  btn.addEventListener('click', function(e){
    e.preventDefault();
    e.stopPropagation();
    resetFxSliderValue(id, key, btn);
  });
  el.parentElement.appendChild(btn);
}
// 当前控制台分页。
var fxPanelTab = 'presets';
// 设置控制台当前分页。
function setFxPanelTab(tab) {
  // 允许的分页 key。
  var allowed = { presets:1, appearance:1, lyrics:1, motion:1, advanced:1 };
  fxPanelTab = allowed[tab] ? tab : 'presets';
  // 控制台面板。
  var panel = document.getElementById('fx-panel');
  if (panel) panel.setAttribute('data-active-tab', fxPanelTab);
  // 标签按钮状态。
  document.querySelectorAll('#fx-panel-tabs [data-fx-tab]').forEach(function(btn){
    btn.classList.toggle('active', btn.getAttribute('data-fx-tab') === fxPanelTab);
  });
  // 分页内容状态。
  document.querySelectorAll('#fx-panel .fx-tab-page').forEach(function(page){
    page.classList.toggle('active', page.getAttribute('data-fx-page') === fxPanelTab);
  });
  repositionFxFloatingPanels();
}
// 从控制台节点中查找第一个输入控件 id。
function fxPanelInputId(node) {
  // 节点内部的输入控件。
  var input = node && node.querySelector ? node.querySelector('input[id]') : null;
  return input ? input.id : '';
}
// 判断控制台节点应该归入哪个分页。
function fxPanelTargetForNode(node, current) {
  if (!node) return current || 'presets';
  // 节点自身 id。
  var id = node.id || '';
  // 节点内部输入 id。
  var inputId = fxPanelInputId(node);
  if (id === 'preset-grid' || id === 'user-archive-grid') return 'presets';
  if (id === 'fx-lyric-fold') return 'lyrics';
  if (id === 'fx-overlay-fold' || id === 'fx-stage-fold') return 'motion';
  if (id === 'fx-advanced' || node.classList.contains('fx-actions')) return 'advanced';
  if (node.classList.contains('lyric-color-row') || node.classList.contains('cover-color-pop') || node.classList.contains('color-lab-pop') || node.classList.contains('cover-color-loupe')) return 'appearance';
  if (inputId === 'fx-bgopacity' || inputId === 'fx-glassaberration') return 'appearance';
  if (inputId === 'fx-lyricglow') return 'lyrics';
  if (/^fx-(intensity|depth|coverres|cineshake)$/.test(inputId)) return 'motion';
  return current || 'presets';
}
// 将原始控制台 DOM 整理为分页结构。
function organizeFxPanel() {
  // 控制台面板。
  var panel = document.getElementById('fx-panel');
  if (!panel) return;
  if (panel._fxPanelOrganized) {
    setFxPanelTab(fxPanelTab);
    return;
  }
  // 控制台头部。
  var head = panel.querySelector('.fx-head');
  // 分页元信息。
  var tabMeta = [
    ['presets', '\u9884\u8bbe'],
    ['appearance', '\u5916\u89c2'],
    ['lyrics', '\u6b4c\u8bcd'],
    ['motion', '\u52a8\u6001'],
    ['advanced', '\u9ad8\u7ea7']
  ];
  // 分页标签容器。
  var tabs = document.createElement('div');
  tabs.className = 'fx-panel-tabs';
  tabs.id = 'fx-panel-tabs';
  tabMeta.forEach(function(meta){
    // 单个分页按钮。
    var btn = document.createElement('button');
    btn.type = 'button';
    btn.setAttribute('data-fx-tab', meta[0]);
    btn.textContent = meta[1];
    tabs.appendChild(btn);
  });
  if (head && head.nextSibling) panel.insertBefore(tabs, head.nextSibling);
  else panel.insertBefore(tabs, panel.firstChild);
  // 分页内容容器表。
  var pages = {};
  // 插入参考节点。
  var insertAfter = tabs;
  tabMeta.forEach(function(meta){
    // 单个分页内容容器。
    var page = document.createElement('div');
    page.className = 'fx-tab-page';
    page.setAttribute('data-fx-page', meta[0]);
    insertAfter.parentNode.insertBefore(page, insertAfter.nextSibling);
    insertAfter = page;
    pages[meta[0]] = page;
  });
  // 原始内容节点列表。
  var original = Array.prototype.slice.call(panel.children).filter(function(child){
    return child !== head && child !== tabs && !child.classList.contains('fx-tab-page');
  });
  // 当前节点默认归属分页。
  var current = 'presets';
  original.forEach(function(node, idx){
    // 目标分页。
    var target;
    if (node.classList.contains('fx-section-label')) {
      target = fxPanelTargetForNode(original[idx + 1], current);
      current = target;
    } else {
      target = fxPanelTargetForNode(node, current);
      current = target;
    }
    (pages[target] || pages.presets).appendChild(node);
  });
  // 默认展开折叠分组，分页后由 tab 控制显示。
  ['fx-lyric-fold','fx-overlay-fold','fx-stage-fold','fx-advanced'].forEach(function(id){
    var fold = document.getElementById(id);
    if (fold) fold.classList.add('open');
  });
  // 绑定分页按钮点击。
  tabs.addEventListener('click', function(e){
    var btn = e.target && e.target.closest ? e.target.closest('[data-fx-tab]') : null;
    if (!btn) return;
    setFxPanelTab(btn.getAttribute('data-fx-tab'));
  });
  // 标记控制台已整理。
  panel._fxPanelOrganized = true;
  setFxPanelTab(fxPanelTab);
}

// 获取控制台控件所在的视觉块节点。
function fxControlBlock(id) {
  // 目标元素。
  var el = document.getElementById(id);
  if (!el) return null;
  return el.closest('.fx-slider,.lyric-color-row,.lyric-color-grid,.fx-seg,.preset-grid,.user-archive-grid,.fx-font-grid') || el;
}
// 在指定控件块前确保有分区标题。
function setFxSectionBefore(id, text) {
  // 控件块。
  var block = fxControlBlock(id);
  if (!block || !block.parentNode) return;
  // 前一个兄弟节点。
  var prev = block.previousElementSibling;
  if (!prev || !prev.classList || !prev.classList.contains('fx-section-label')) {
    // 不存在分区标题时创建。
    prev = document.createElement('div');
    prev.className = 'fx-section-label';
    block.parentNode.insertBefore(prev, block);
  }
  prev.textContent = text;
}
// 设置指定滑块的 label 文案。
function setFxSliderLabel(id, text) {
  // 控件块。
  var block = fxControlBlock(id);
  // 控件 label。
  var label = block && block.querySelector ? block.querySelector('label') : null;
  if (label) label.textContent = text;
}
// 在指定节点前确保有分区标题。
function setFxSectionBeforeNode(node, text) {
  if (!node || !node.parentNode) return;
  // 前一个兄弟节点。
  var prev = node.previousElementSibling;
  if (!prev || !prev.classList || !prev.classList.contains('fx-section-label')) {
    // 不存在分区标题时创建。
    prev = document.createElement('div');
    prev.className = 'fx-section-label';
    node.parentNode.insertBefore(prev, node);
  }
  prev.textContent = text;
}
// 将开关按钮移动到指定网格。
function moveToggleToGrid(toggleId, grid) {
  // 开关节点。
  var node = document.getElementById(toggleId);
  if (!node || !grid || node.parentNode === grid) return;
  grid.appendChild(node);
}
// 确保歌词核心开关被归入歌词开关网格。
function ensureLyricPrimaryControls() {
  // 歌词折叠区内容。
  var body = document.querySelector('#fx-lyric-fold .fx-fold-body');
  if (!body) return;
  // 歌词核心开关网格。
  var grid = document.getElementById('fx-lyric-primary-controls');
  if (!grid) {
    // 分区标题。
    var label = document.createElement('div');
    label.className = 'fx-section-label';
    label.id = 'fx-lyric-primary-label';
    label.textContent = '歌词开关';
    // 新建开关网格。
    grid = document.createElement('div');
    grid.className = 'fx-toggle-grid lyric-primary-toggle-grid';
    grid.id = 'fx-lyric-primary-controls';
    body.insertBefore(grid, body.firstChild);
    body.insertBefore(label, grid);
  }
  // 把相关开关移动到歌词主开关网格。
  [
    't-lyricCameraLock',
    't-lyricGlow',
    't-lyricGlowBeat',
    't-lyricGlowParticles'
  ].forEach(function(id){ moveToggleToGrid(id, grid); });
}
// 给背景媒体控件添加上传提示。
function applyBackgroundMediaHint() {
  // 背景媒体值节点。
  var value = document.getElementById('bg-image-value');
  if (value && !value.dataset.mediaHint) {
    value.dataset.mediaHint = '1';
    value.title = '支持图片 JPG / PNG / WebP 与视频 MP4 / WebM / MOV 上传';
  }
  // 背景媒体所在 label。
  var label = value && value.closest ? value.closest('.fx-color-row-label') : null;
  if (label && !document.getElementById('bg-media-hint')) {
    // 小提示节点。
    var hint = document.createElement('small');
    hint.id = 'bg-media-hint';
    hint.textContent = '支持图片 / 视频上传';
    label.appendChild(hint);
  }
}
// 重命名和整理视觉控制台中的分区和控件标签。
function relabelFxPanelControls() {
  // 控制台标题。
  var title = document.querySelector('#fx-panel .fx-title');
  if (title) title.textContent = '视觉控制台';
  ensureLyricPrimaryControls();
  applyBackgroundMediaHint();
  // 叠加开关所在网格。
  var overlayGrid = document.getElementById('t-cinema');
  overlayGrid = overlayGrid && overlayGrid.closest('.fx-toggle-grid');
  // 分区标题。
  setFxSectionBeforeNode(overlayGrid, '镜头与叠加');
  setFxSectionBefore('preset-grid', '预设与存档');
  setFxSectionBefore('user-archive-grid', '用户存档');
  setFxSectionBefore('ui-accent-picker', '界面与背景');
  setFxSectionBefore('fx-intensity', '画面基础');
  setFxSectionBefore('fx-lyricglow', '歌词溢光强度');
  setFxSectionBefore('lyric-color-grid', '文字颜色');
  setFxSectionBefore('lyric-highlight-picker', '跟唱高亮');
  setFxSectionBefore('lyric-glow-row', '歌词溢光颜色');
  setFxSectionBefore('lyric-font-grid', '字体与字距');
  setFxSectionBefore('fx-lyricscale', '位置与角度');
  setFxSectionBefore('shelf-seg', '3D 歌单架');
  setFxSectionBefore('shelf-camera-seg', '歌单架镜头');
  setFxSectionBefore('shelf-presence-seg', '歌单架显示');
  setFxSectionBefore('shelf-accent-picker', '歌单架外观');
  setFxSectionBefore('fx-shelfsize', '歌单架参数');
  setFxSectionBefore('fx-point', '粒子高级参数');
  setFxSliderLabel('fx-intensity', '律动强度');
  setFxSliderLabel('fx-depth', '画面景深');
  setFxSliderLabel('fx-coverres', '封面清晰度');
  setFxSliderLabel('fx-cineshake', '电影镜头');
  setFxSliderLabel('fx-lyricglow', '溢光强度');
  setFxSliderLabel('fx-bgopacity', '背景透明度');
  setFxSliderLabel('fx-glassaberration', '玻璃色差');
  setFxSliderLabel('fx-lyricspacing', '字间距');
  setFxSliderLabel('fx-lyriclineheight', '行距');
  setFxSliderLabel('fx-lyricweight', '字重');
  setFxSliderLabel('fx-lyricscale', '歌词大小');
  setFxSliderLabel('fx-lyricx', '左右位置');
  setFxSliderLabel('fx-lyricy', '上下位置');
  setFxSliderLabel('fx-lyricz', '前后景深');
  setFxSliderLabel('fx-lyrictiltx', '上下旋转');
  setFxSliderLabel('fx-lyrictilty', '左右旋转');
  setFxSliderLabel('fx-wallpaperopacity', '壁纸透明度');
  setFxSliderLabel('fx-shelfsize', '歌单架大小');
  setFxSliderLabel('fx-shelfx', '左右位置');
  setFxSliderLabel('fx-shelfy', '上下位置');
  setFxSliderLabel('fx-shelfz', '前后景深');
  setFxSliderLabel('fx-shelfangle', '侧向角度');
  setFxSliderLabel('fx-shelfopacity', '整体透明度');
  setFxSliderLabel('fx-shelfbgalpha', '背景透明度');
  setFxSliderLabel('fx-point', '粒子尺寸');
  setFxSliderLabel('fx-speed', '运动速度');
  setFxSliderLabel('fx-twist', '粒子扭曲');
  setFxSliderLabel('fx-color', '色彩张力');
  setFxSliderLabel('fx-bloom', '光晕强度');
  setFxSliderLabel('fx-scatter', '离散感');
  setFxSliderLabel('fx-bgfade', '背景压暗');
}

// 初始化并绑定视觉控制台所有交互。
function bindFxPanel() {
  liftFxFloatingPopups();
  organizeFxPanel();
  relabelFxPanelControls();
  buildPresetGrid();
  renderUserFxArchives();
  buildLyricColorControls();
  // 滑块 id 与 fx 字段映射。
  var ids = [
    ['fx-intensity','intensity'],['fx-depth','depth'],['fx-coverres','coverResolution'],['fx-cineshake','cinemaShake'],['fx-lyricglow','lyricGlowStrength'],['fx-bgopacity','backgroundOpacity'],['fx-glassaberration','controlGlassChromaticOffset'],
    ['fx-wallpaperopacity','wallpaperOpacity'],
    ['fx-shelfsize','shelfSize'],['fx-shelfx','shelfOffsetX'],['fx-shelfy','shelfOffsetY'],['fx-shelfz','shelfOffsetZ'],['fx-shelfangle','shelfAngleY'],['fx-shelfopacity','shelfOpacity'],['fx-shelfbgalpha','shelfBgOpacity'],
    ['fx-lyricspacing','lyricLetterSpacing'],['fx-lyriclineheight','lyricLineHeight'],['fx-lyricweight','lyricWeight'],
    ['fx-lyricscale','lyricScale'],['fx-lyricx','lyricOffsetX'],['fx-lyricy','lyricOffsetY'],['fx-lyricz','lyricOffsetZ'],['fx-lyrictiltx','lyricTiltX'],['fx-lyrictilty','lyricTiltY'],
    ['fx-point','point'],['fx-speed','speed'],['fx-twist','twist'],
    ['fx-color','color'],['fx-bloom','bloomStrength'],['fx-scatter','scatter'],['fx-bgfade','bgFade'],
  ];
  ids.forEach(function(pair){
    // 当前滑块。
    var el = document.getElementById(pair[0]);
    if (!el) return;
    ensureFxSliderResetButton(pair[0], pair[1]);
    el.addEventListener('input', function(){
      // 将滑块值写入对应 fx 字段。
      fx[pair[1]] = parseFloat(el.value);
      // 输出文本节点。
      var out = el.parentElement.querySelector('output');
      if (pair[1] === 'coverResolution') {
        // 封面粒子分辨率变化需要重建封面粒子。
        fx.coverResolution = normalizeCoverResolution(fx.coverResolution);
        applyCoverParticleResolution(fx.coverResolution, { reload: true });
      }
      // 字重按 50 的步进吸附。
      if (pair[1] === 'lyricWeight') fx.lyricWeight = Math.round(clampRange(fx.lyricWeight, 500, 900) / 50) * 50;
      if (pair[1] === 'backgroundOpacity') {
        // 调整背景透明度时进入自定义背景模式。
        fx.backgroundOpacity = clampRange(fx.backgroundOpacity, 0, 1);
        fx.backgroundColorMode = 'custom';
        fx.backgroundColorCustom = true;
        updateCustomBackgroundControls();
      }
      if (pair[1] === 'controlGlassChromaticOffset') {
        // 玻璃色差需要同步 SVG filter。
        fx.controlGlassChromaticOffset = normalizeControlGlassChromaticOffset(fx.controlGlassChromaticOffset);
        applyControlGlassChromaticOffset();
      }
      // 各特殊滑块范围夹紧。
      if (pair[1] === 'wallpaperOpacity') fx.wallpaperOpacity = clampRange(fx.wallpaperOpacity, 0.35, 1);
      if (pair[1] === 'shelfSize') fx.shelfSize = clampRange(fx.shelfSize, 0.65, 1.45);
      if (pair[1] === 'shelfOffsetX') fx.shelfOffsetX = clampRange(fx.shelfOffsetX, -1.2, 1.2);
      if (pair[1] === 'shelfOffsetY') fx.shelfOffsetY = clampRange(fx.shelfOffsetY, -0.9, 0.9);
      if (pair[1] === 'shelfOffsetZ') fx.shelfOffsetZ = clampRange(fx.shelfOffsetZ, -0.9, 0.9);
      if (pair[1] === 'shelfAngleY') {
        fx.shelfAngleYManual = true;
        fx.shelfAngleY = Math.round(clampRange(fx.shelfAngleY, -30, 30));
      }
      if (pair[1] === 'shelfOpacity') fx.shelfOpacity = clampRange(fx.shelfOpacity, 0.25, 1);
      if (pair[1] === 'shelfBgOpacity') fx.shelfBgOpacity = clampRange(fx.shelfBgOpacity, 0.25, 0.98);
      if (pair[1] === 'lyricTiltX' || pair[1] === 'lyricTiltY') fx[pair[1]] = Math.round(clampRange(fx[pair[1]], -42, 42));
      if (out) out.textContent = pair[1] === 'coverResolution'
        ? coverParticleCountLabel(fx.coverResolution)
        : (pair[1] === 'lyricWeight' || pair[1] === 'controlGlassChromaticOffset' || pair[1] === 'lyricTiltX' || pair[1] === 'lyricTiltY' || pair[1] === 'shelfAngleY' ? String(Math.round(fx[pair[1]])) : Number(el.value).toFixed(pair[1] === 'lyricLetterSpacing' ? 3 : 2));
      syncFxUniforms();
      // 歌单架相关滑块变化后刷新歌单架主题。
      if (/^shelf(Size|OffsetX|OffsetY|OffsetZ|AngleY|Opacity|BgOpacity)$/.test(pair[1]) && shelfManager && shelfManager.refreshTheme) shelfManager.refreshTheme();
      // 歌词排版变化后刷新当前歌词 mesh。
      if (pair[1] === 'lyricLetterSpacing' || pair[1] === 'lyricLineHeight' || pair[1] === 'lyricWeight') refreshCurrentLyricStyle();
      // 壁纸透明度变化需要推送壁纸状态。
      if (pair[1] === 'wallpaperOpacity') pushWallpaperState(true);
      saveLyricLayout();
    });
  });
  // 歌词主色选择器。
  var lyricPicker = document.getElementById('lyric-color-picker');
  if (lyricPicker) {
    lyricPicker.addEventListener('input', function(){ setLyricColorCustom(lyricPicker.value, true); });
    lyricPicker.addEventListener('change', function(){ showToast('歌词颜色: ' + normalizeHexColor(lyricPicker.value).toUpperCase()); });
  }
  // 歌词高亮色选择器。
  var lyricHighlightPicker = document.getElementById('lyric-highlight-picker');
  if (lyricHighlightPicker) {
    lyricHighlightPicker.addEventListener('input', function(){ setLyricHighlightCustom(lyricHighlightPicker.value, true); });
    lyricHighlightPicker.addEventListener('change', function(){ showToast('高亮颜色: ' + normalizeHexColor(lyricHighlightPicker.value).toUpperCase()); });
  }
  // 歌词溢光色选择器。
  var lyricGlowPicker = document.getElementById('lyric-glow-picker');
  if (lyricGlowPicker) {
    lyricGlowPicker.addEventListener('input', function(){ setLyricGlowCustom(lyricGlowPicker.value, true); });
    lyricGlowPicker.addEventListener('change', function(){ showToast('溢光颜色: ' + normalizeHexColor(lyricGlowPicker.value).toUpperCase()); });
  }
  // UI 强调色选择器。
  var uiAccentPicker = document.getElementById('ui-accent-picker');
  if (uiAccentPicker) {
    uiAccentPicker.addEventListener('input', function(){ setUiAccentColor(uiAccentPicker.value, true); });
    uiAccentPicker.addEventListener('change', function(){ showToast('界面高亮: ' + normalizeHexColor(uiAccentPicker.value, '#00f5d4').toUpperCase()); });
  }
  // 视觉主色选择器。
  var visualTintPicker = document.getElementById('visual-tint-picker');
  if (visualTintPicker) {
    visualTintPicker.addEventListener('input', function(){ setVisualTintCustom(visualTintPicker.value, true); });
    visualTintPicker.addEventListener('change', function(){ showToast('视觉主色: ' + normalizeHexColor(visualTintPicker.value).toUpperCase()); });
  }
  // 视觉图标颜色选择器。
  var visualIconPicker = document.getElementById('visual-icon-picker');
  if (visualIconPicker) {
    visualIconPicker.addEventListener('input', function(){ setVisualIconColor(visualIconPicker.value, true); });
    visualIconPicker.addEventListener('change', function(){ showToast('视觉图标: ' + normalizeHexColor(visualIconPicker.value, '#7fd8ff').toUpperCase()); });
  }
  // 背景颜色选择器。
  var bgColorPicker = document.getElementById('bg-color-picker');
  if (bgColorPicker) {
    bgColorPicker.addEventListener('input', function(){ setCustomBackgroundColor(bgColorPicker.value, true); });
    bgColorPicker.addEventListener('change', function(){ showToast('背景颜色: ' + normalizeHexColor(bgColorPicker.value, '#000000').toUpperCase()); });
  }
  // 歌单架强调色选择器。
  var shelfAccentPicker = document.getElementById('shelf-accent-picker');
  if (shelfAccentPicker) {
    shelfAccentPicker.addEventListener('input', function(){ setShelfAccentColor(shelfAccentPicker.value, true); });
    shelfAccentPicker.addEventListener('change', function(){ showToast('歌单架颜色: ' + shelfAccentHex().toUpperCase()); });
  }
  // 背景媒体文件输入。
  var bgImageInput = document.getElementById('background-image-input');
  if (bgImageInput) {
    bgImageInput.addEventListener('change', function(e){
      // 用户选择的背景媒体文件。
      var file = e.target.files && e.target.files[0];
      if (file) readBackgroundMediaFile(file);
      e.target.value = '';
    });
  }
  ['ui-accent-picker','visual-tint-picker','visual-icon-picker','bg-color-picker','shelf-accent-picker','lyric-color-picker','lyric-highlight-picker','lyric-glow-picker'].forEach(function(id){
    // 给每个颜色输入绑定颜色实验室弹层。
    bindColorLabPicker(document.getElementById(id));
  });
  bindColorLabRows();
  // 颜色实验室饱和度/明度区域。
  var sv = document.getElementById('color-lab-sv');
  if (sv && !sv._bound) {
    // 防重复绑定标记。
    sv._bound = true;
    sv.addEventListener('pointerdown', function(e){
      e.preventDefault();
      colorLabState.dragging = true;
      sv.setPointerCapture && sv.setPointerCapture(e.pointerId);
      updateColorLabFromSv(e);
    });
    sv.addEventListener('pointermove', function(e){ if (colorLabState.dragging) updateColorLabFromSv(e); });
    sv.addEventListener('pointerup', function(){ colorLabState.dragging = false; });
    sv.addEventListener('pointercancel', function(){ colorLabState.dragging = false; });
  }
  // 颜色实验室色相滑块。
  var hue = document.getElementById('color-lab-hue');
  if (hue && !hue._bound) {
    // 防重复绑定标记。
    hue._bound = true;
    hue.addEventListener('input', function(){
      colorLabState.h = clampRange(Number(hue.value) || 0, 0, 360) / 360;
      // 根据 HSV 状态计算当前颜色。
      var hex = hsvToHex(colorLabState.h, colorLabState.s, colorLabState.v);
      syncColorLabUi(hex);
      applyColorLabValue(hex, true);
    });
  }
  // 颜色实验室十六进制输入框。
  var hexInput = document.getElementById('color-lab-hex');
  if (hexInput && !hexInput._bound) {
    // 防重复绑定标记。
    hexInput._bound = true;
    hexInput.addEventListener('change', function(){
      // 输入色值归一化。
      var hex = normalizeHexColor(hexInput.value || '#000000', '#000000');
      syncColorLabUi(hex);
      applyColorLabValue(hex);
    });
  }
  // 颜色实验室预设色容器。
  var presets = document.getElementById('color-lab-presets');
  if (presets && !presets._bound) {
    // 防重复绑定标记。
    presets._bound = true;
    presets.addEventListener('click', function(e){
      // 命中的预设色按钮。
      var btn = e.target && e.target.closest ? e.target.closest('[data-color]') : null;
      if (!btn) return;
      // 预设色值。
      var hex = normalizeHexColor(btn.getAttribute('data-color') || '#000000', '#000000');
      syncColorLabUi(hex);
      applyColorLabValue(hex);
    });
  }
  if (!document._colorLabOutsideBound) {
    // 全局只绑定一次颜色弹层外部点击关闭。
    document._colorLabOutsideBound = true;
    document.addEventListener('mousedown', function(e){
      // 颜色实验室弹层。
      var pop = document.getElementById('color-lab-pop');
      if (!pop || !pop.classList.contains('show')) return;
      if (e.target && (e.target.closest('#color-lab-pop') || e.target.closest('.lyric-color-picker') || e.target.closest('.lyric-color-row'))) return;
      closeColorLab();
    }, true);
    document.addEventListener('mousedown', function(e){
      // 封面取色弹层。
      var pop = document.getElementById('cover-color-pop');
      if (!pop || !pop.classList.contains('show')) return;
      if (e.target && (e.target.closest('#cover-color-pop') || e.target.closest('#visual-tint-auto-btn'))) return;
      closeCoverColorPicker();
    }, true);
  }
  // 三态
  // 歌单架模式按钮。
  document.querySelectorAll('#shelf-seg button').forEach(function(b){
    b.addEventListener('click', function(){ setShelfMode(b.dataset.shelf); });
  });
  // 歌单架镜头模式按钮。
  document.querySelectorAll('#shelf-camera-seg [data-shelf-camera]').forEach(function(b){
    b.addEventListener('click', function(){ setShelfCameraMode(b.getAttribute('data-shelf-camera')); });
  });
  // 歌单架显示策略按钮。
  document.querySelectorAll('#shelf-presence-seg [data-shelf-presence]').forEach(function(b){
    b.addEventListener('click', function(){ setShelfPresence(b.getAttribute('data-shelf-presence')); });
  });
  // 后台策略按钮。
  document.querySelectorAll('#performance-background-seg [data-performance-background]').forEach(function(btn){
    btn.addEventListener('click', function(){
      setPerformanceBackgroundMode(btn.getAttribute('data-performance-background'));
    });
  });
  // 画质档位按钮。
  document.querySelectorAll('#performance-quality-seg [data-performance-quality]').forEach(function(btn){
    btn.addEventListener('click', function(){
      setPerformanceQualityMode(btn.getAttribute('data-performance-quality'));
    });
  });
  updateFxInputs();
}
// 切换布尔型视觉功能开关。
function toggleFx(key) {
  if (isDevelopmentLockedFx(key)) {
    // 开发锁功能不能开启，恢复合法状态并提示用户。
    normalizeDevelopmentLockedFxState();
    saveLyricLayout();
    updateFxInputs();
    applyWallpaperModeState(true);
    showToast('开发中，暂不可用');
    return;
  }
  fx[key] = !fx[key];
  // 根据字段名映射到对应开关 DOM id。
  var toggleId = 't-' + (key === 'floatLayer' ? 'float' : key === 'aiDepth' ? 'aidepth' : key);
  // 对应开关节点。
  var toggle = document.getElementById(toggleId);
  if (toggle) toggle.classList.toggle('on', fx[key]);
  syncFxUniforms();
  if (key === 'lyricCameraLock' || key === 'lyricGlow' || key === 'lyricGlowBeat' || key === 'lyricGlowParticles' || key === 'bloom' || key === 'edge' || key === 'cinema' || key === 'wallpaperMode' || key === 'liveBackgroundKeep') saveLyricLayout();
  // 浮空粒子层需要同步创建或销毁。
  if (key === 'floatLayer') { if (fx.floatLayer) createFloatLayer(); else destroyFloatLayer(); }
  if (key === 'wallpaperMode') applyWallpaperModeState(true);
  if (key === 'liveBackgroundKeep') {
    // 旧直播后台保持开关同步到新的后台策略。
    fx.performanceBackground = fx.liveBackgroundKeep ? 'keep' : 'auto';
    updatePerformanceControls();
    saveLyricLayout();
    if (fx.liveBackgroundKeep && backgroundCacheTrimTimer) {
      clearTimeout(backgroundCacheTrimTimer);
      backgroundCacheTrimTimer = 0;
    }
    updateRenderPowerClasses();
    applyRendererPowerMode();
    if (fx.liveBackgroundKeep) recoverVisualsAfterBackground('live-background-keep');
  }
  if (key === 'lyricGlow') showToast(fx.lyricGlow ? '歌词溢光已开启' : '歌词溢光已关闭');
  if (key === 'lyricGlowBeat') showToast(fx.lyricGlowBeat ? '歌词溢光跟随鼓点' : '歌词溢光已脱离鼓点');
  if (key === 'lyricGlowParticles') showToast(fx.lyricGlowParticles ? '歌词光粒已开启' : '歌词光粒已关闭');
  if (key === 'wallpaperMode') showToast(fx.wallpaperMode ? '壁纸模式已开启' : '壁纸模式已关闭');
  if (key === 'liveBackgroundKeep') showToast(fx.liveBackgroundKeep ? '直播后台保持已开启' : '直播后台保持已关闭');
  if (key === 'lyricCameraLock') showToast(fx.lyricCameraLock ? '歌词已绑定镜头' : '歌词已恢复自由漂浮');
  if (key === 'bloom') showToast(fx.bloom ? '溢光已开启' : '溢光已关闭');
  if (key === 'edge') showToast(fx.edge ? '已开启轮廓高亮' : '已关闭轮廓高亮');
  if (key === 'cinema') showToast(fx.cinema ? '已开启电影镜头' : '已关闭电影镜头');
  if (key === 'aiDepth') {
    if (fx.aiDepth) {
      // 重新开启 AI 深度时清除失败冷却并尝试处理当前封面。
      aiDepthFailUntil = 0;
      queueAIDepthForCurrentCover(true);
    }
    showToast(fx.aiDepth ? '已开启后台 AI 立体增强' : '已关闭 AI 立体增强, 使用轻量弧面');
  }
}
// 切换视觉控制台显示状态。
function toggleFxPanel(force) {
  // 控制台面板。
  var el = document.getElementById('fx-panel');
  if (!el) return;
  // 当前是否打开或处于 peek 状态。
  var currentlyOpen = el.classList.contains('show') || el.classList.contains('peek');
  if (peekTimers && peekTimers.fx) { clearTimeout(peekTimers.fx); peekTimers.fx = null; }
  fxPanelPinned = false;
  if (force === false) {
    // 强制关闭时播放 closing 状态。
    el.classList.remove('show', 'peek');
    el.classList.toggle('closing', currentlyOpen);
    setTimeout(function(){ el.classList.remove('closing'); }, 280);
    // 同步悬浮按钮状态。
    var fab = document.getElementById('fx-fab');
    if (fab) fab.classList.remove('active');
    return;
  }
  // 其它情况进入 peek 状态。
  el.classList.remove('show', 'closing');
  setPeek(el, true, 'fx');
}
// 恢复视觉参数到默认值，同时保留歌单架显示配置。
function resetFx() {
  // 当前歌单架模式。
  var savedShelf = fx.shelf;
  // 当前歌单架镜头模式。
  var savedShelfCameraMode = normalizeShelfCameraMode(fx.shelfCameraMode || fxDefaults.shelfCameraMode);
  // 当前歌单架显示策略。
  var savedShelfPresence = normalizeShelfPresence(fx.shelfPresence || fxDefaults.shelfPresence);
  fx = Object.assign({}, fxDefaults, {
    shelf: savedShelf,
    shelfCameraMode: savedShelfCameraMode,
    shelfPresence: savedShelfPresence,
    shelfAngleY: shelfDefaultAngleForCameraMode(savedShelfCameraMode),
    shelfAngleYManual: false
  });
  applyCoverParticleResolution(fx.coverResolution, { reload: true });
  updateFxInputs();
  applyWallpaperModeState(true);
  updateRenderPowerClasses();
  applyRendererPowerMode();
  setStageLyricPalette(stageLyrics.coverPalette || stageLyrics.palette);
  setPreset(fx.preset, { silent: true, preserveCamera: true, skipTransition: true });
  if (fx.floatLayer) createFloatLayer(); else destroyFloatLayer();
  if (shelfManager && shelfManager.rebuild) shelfManager.rebuild(true);
  if (shelfManager && shelfManager.refreshTheme) shelfManager.refreshTheme();
  saveLyricLayout();
  showToast('已恢复默认参数');
}

// 设置 3D 歌单架模式。
function setShelfMode(m) {
  // 归一化目标模式。
  m = /^(off|side|stage)$/.test(String(m || '')) ? m : fxDefaults.shelf;
  fx.shelf = m;
  document.querySelectorAll('#shelf-seg button').forEach(function(b){ b.classList.toggle('active', b.dataset.shelf === m); });
  if (shelfManager) shelfManager.setMode(m);
  // 舞台模式: 底部控件让位
  // 底部控制条节点。
  var bottomBar = document.getElementById('bottom-bar');
  if (bottomBar) bottomBar.classList.toggle('stage-mode', m === 'stage');
  saveLyricLayout();
}

// 刷新歌单架控制相关 UI。
function updateShelfControlUi() {
  fx.shelfCameraMode = normalizeShelfCameraMode(fx.shelfCameraMode || fxDefaults.shelfCameraMode);
  fx.shelfPresence = normalizeShelfPresence(fx.shelfPresence || fxDefaults.shelfPresence);
  // 歌单架镜头模式按钮。
  document.querySelectorAll('#shelf-camera-seg [data-shelf-camera]').forEach(function(btn){
    btn.classList.toggle('active', btn.getAttribute('data-shelf-camera') === fx.shelfCameraMode);
  });
  // 歌单架显示策略按钮。
  document.querySelectorAll('#shelf-presence-seg [data-shelf-presence]').forEach(function(btn){
    btn.classList.toggle('active', btn.getAttribute('data-shelf-presence') === fx.shelfPresence);
  });
  // 当前歌单架强调色。
  var color = shelfAccentHex();
  // 歌单架强调色选择器。
  var picker = document.getElementById('shelf-accent-picker');
  // 歌单架强调色文本。
  var value = document.getElementById('shelf-accent-value');
  if (picker) picker.value = color;
  if (value) value.textContent = color.toUpperCase();
}
// 刷新歌单架视觉状态。
function refreshShelfVisuals(reason) {
  updateShelfControlUi();
  if (shelfManager && shelfManager.refreshTheme) shelfManager.refreshTheme();
  if (shelfManager && shelfManager.rebuild && reason === 'mode') shelfManager.rebuild(true);
}
// 设置歌单架镜头模式。
function setShelfCameraMode(mode) {
  fx.shelfCameraMode = normalizeShelfCameraMode(mode);
  applyShelfCameraDefaultAngle(true);
  setRange('fx-shelfangle', fx.shelfAngleY);
  updateShelfControlUi();
  if (fx.shelfCameraMode === 'static' && orbit && orbit.focus && /^shelf-/.test(String(orbit.focus.type || ''))) {
    setFocusZone(null, true);
  }
  saveLyricLayout();
  showToast(fx.shelfCameraMode === 'static' ? '3D歌单架: 静态镜头' : '3D歌单架: 动态镜头');
}
// 设置歌单架显示策略。
function setShelfPresence(mode) {
  fx.shelfPresence = normalizeShelfPresence(mode);
  updateShelfControlUi();
  if (shelfManager && shelfManager.setMode) shelfManager.setMode(fx.shelf);
  if (fx.shelfPresence === 'auto' && !shelfPinnedOpen) {
    shelfHoverCue.target = 0;
  }
  saveLyricLayout();
  showToast(fx.shelfPresence === 'always' ? '3D歌单架: 常驻' : '3D歌单架: 自动隐藏');
}
// 设置歌单架强调色。
function setShelfAccentColor(color, silent) {
  fx.shelfAccentColor = normalizeHexColor(color || fxDefaults.shelfAccentColor, fxDefaults.shelfAccentColor);
  refreshShelfVisuals('color');
  saveLyricLayout();
  if (!silent) showToast('歌单架颜色: ' + fx.shelfAccentColor.toUpperCase());
}
// 重置歌单架强调色。
function resetShelfAccentColor() {
  setShelfAccentColor(fxDefaults.shelfAccentColor || '#f4d28a');
}

// 同步控制条自动隐藏按钮状态。
function syncControlsAutoHideButton() {
  // 控制条隐藏按钮。
  var btn = document.getElementById('controls-hide-btn');
  if (btn) btn.classList.toggle('active', controlsAutoHide);
  if (!controlsAutoHide && controlsHideTimer) {
    clearTimeout(controlsHideTimer);
    controlsHideTimer = null;
  }
}

// 静默设置舞台歌词粒子开关。
function setParticleLyricsSilently(on) {
  fx.particleLyrics = !!on;
  if (fx.particleLyrics) createLyricsParticles();
  else clearStageLyrics();
  lyricsVisible = fx.particleLyrics;
}

// 刷新沉浸模式按钮状态。
function updateImmersiveButton() {
  // 沉浸模式按钮。
  var btn = document.getElementById('immersive-btn');
  if (!btn) return;
  btn.classList.toggle('active', immersiveMode);
  btn.setAttribute('aria-pressed', immersiveMode ? 'true' : 'false');
  btn.title = immersiveMode ? '退出全沉浸式' : '全沉浸式';
  btn.setAttribute('aria-label', btn.title);
}

// 关闭进入沉浸模式时会干扰画面的弹层和提示。
function closeImmersiveInterference() {
  closeMiniQueue();
  ['ai-depth-chip', 'beat-chip'].forEach(function(id){
    // 需要隐藏的提示节点。
    var el = document.getElementById(id);
    if (el) el.classList.remove('peek', 'show', 'closing');
  });
  setFocusZone(null, true);
}

// 设置全沉浸模式开关。
function setImmersiveMode(on) {
  on = !!on;
  if (immersiveMode === on) return;

  if (on) {
    // 进入沉浸前保存可恢复状态。
    immersiveState = {
      shelfMode: fx.shelf,
      shelfPinnedOpen: shelfPinnedOpen,
      lyrics: fx.particleLyrics,
      controlsAutoHide: controlsAutoHide,
      bottomVisible: !!(document.getElementById('bottom-bar') && document.getElementById('bottom-bar').classList.contains('visible'))
    };
    immersiveMode = true;
    document.body.classList.add('immersive-mode');
    // 进入时确保底部控制条短暂可见。
    var bottomBarEnter = document.getElementById('bottom-bar');
    if (bottomBarEnter) bottomBarEnter.classList.add('visible');
    closeImmersiveInterference();
    if (!fx.particleLyrics) setParticleLyricsSilently(true);
    controlsAutoHide = true;
    syncControlsAutoHideButton();
    updateImmersiveButton();
    syncCursorAutoHideMode();
    revealBottomControls(720);
    setTimeout(function(){
      // 一段时间后自动隐藏底部控制条。
      if (immersiveMode && !controlsHovering) setControlsHidden(true);
    }, 980);
    return;
  }

  // 退出沉浸并恢复保存的状态。
  immersiveMode = false;
  document.body.classList.remove('immersive-mode');
  closeMiniQueue();
  if (immersiveState.shelfMode) setShelfMode(immersiveState.shelfMode);
  if (immersiveState.shelfMode === 'side' && immersiveState.shelfPinnedOpen) setShelfPinnedOpen(true, true);
  else setShelfPinnedOpen(false, true);
  if (immersiveState.lyrics === false) setParticleLyricsSilently(false);
  controlsAutoHide = immersiveState.controlsAutoHide !== false;
  syncControlsAutoHideButton();
  updateImmersiveButton();
  syncCursorAutoHideMode();
  var bottomBarExit = document.getElementById('bottom-bar');
  if (immersiveState.bottomVisible) revealBottomControls(900);
  else if (bottomBarExit) bottomBarExit.classList.remove('visible', 'soft-hidden');
  showToast('已退出全沉浸式');
}

// 切换全沉浸模式。
function toggleImmersiveMode() {
  setImmersiveMode(!immersiveMode);
}

// ===== js/09-account-ui.js =====

// ============================================================
//  模态动画工具
// ============================================================
// 使用 GSAP 打开模态遮罩。
function openGsapModal(mask) {
  if (!mask) return;
  // 模态内容面板。
  var panel = mask.querySelector('.modal');
  mask.classList.add('show');
  if (window.gsap) {
    // 遮罩和面板分别播放淡入与上浮动画。
    window.gsap.killTweensOf(mask);
    if (panel) window.gsap.killTweensOf(panel);
    window.gsap.set(mask, { display: 'flex', visibility: 'visible' });
    window.gsap.fromTo(mask,
      { autoAlpha: 0 },
      { autoAlpha: 1, duration: 0.38, ease: 'power2.out', overwrite: true }
    );
    if (panel) {
      window.gsap.fromTo(panel,
        { autoAlpha: 0, y: 26, scale: 0.965, filter: 'blur(12px)' },
        { autoAlpha: 1, y: 0, scale: 1, filter: 'blur(0px)', duration: 0.68, ease: 'expo.out', overwrite: true }
      );
    }
  } else {
    // 无 GSAP 时直接显示。
    mask.style.display = 'flex';
    mask.style.visibility = 'visible';
    mask.style.opacity = '1';
  }
}
// 使用 GSAP 关闭模态遮罩。
function closeGsapModal(mask, afterClose) {
  if (!mask || !mask.classList.contains('show')) {
    if (afterClose) afterClose();
    return;
  }
  // 模态内容面板。
  var panel = mask.querySelector('.modal');
  // 关闭完成后的收尾。
  function finish() {
    mask.classList.remove('show');
    if (window.gsap) {
      window.gsap.set(mask, { clearProps: 'display,visibility,opacity' });
      if (panel) window.gsap.set(panel, { clearProps: 'opacity,visibility,transform,filter' });
    } else {
      mask.style.display = '';
      mask.style.visibility = '';
      mask.style.opacity = '';
    }
    if (afterClose) afterClose();
  }
  if (window.gsap) {
    // 面板先淡出下沉，遮罩随后整体淡出。
    window.gsap.killTweensOf(mask);
    if (panel) {
      window.gsap.killTweensOf(panel);
      window.gsap.to(panel, { autoAlpha: 0, y: 18, scale: 0.976, filter: 'blur(8px)', duration: 0.28, ease: 'power2.in', overwrite: true });
    }
    window.gsap.to(mask, { autoAlpha: 0, duration: 0.34, ease: 'power2.inOut', overwrite: true, onComplete: finish });
  } else {
    finish();
  }
}
// 绑定模态遮罩点击背景关闭逻辑。
function bindModalBackdropClose() {
  [
  ].forEach(function(pair){
    // 遮罩节点。
    var mask = document.getElementById(pair[0]);
    // 关闭函数。
    var close = pair[1];
    if (!mask || mask.__backdropCloseBound) return;
    mask.__backdropCloseBound = true;
    mask.addEventListener('click', function(e){
      if (e.target === mask) close();
    });
  });
}

// ============================================================
//  空场待机引导
// ============================================================
// 待机引导 canvas。
var idleGuideCanvas = null;
// 待机引导 canvas 绘制上下文。
var idleGuideCtx = null;
// 待机引导画布宽高和 DPR。
var idleGuideW = 0, idleGuideH = 0, idleGuideDpr = 1;
// 待机引导粒子列表。
var idleGuideParticles = [];
// 待机引导拖尾轨迹。
var idleGuideTrails = [[], [], [], []];
// 待机引导启动时间。
var idleGuideStartedAt = performance.now();
// 待机引导是否可见。
var idleGuideVisible = false;
// 待机引导上一帧时间。
var idleGuideLastFrameAt = performance.now();
// 待机引导延迟显示定时器。
var idleGuideDelayTimer = null;
// Keep Wallpaper as the only startup idle background.
// 是否启用待机引导背景；当前关闭，仅保留壁纸启动背景。
var IDLE_GUIDE_BACKGROUND_ENABLED = false;
// 待机引导交互状态。
var idleGuideInteraction = {
  // 绕中心旋转角。
  angle: 0,
  // 当前旋转速度。
  velocity: 0,
  // X 轴旋转。
  rotX: -0.12,
  // Y 轴旋转。
  rotY: 0,
  // X 轴惯性旋转速度。
  spinX: 0,
  // Y 轴惯性旋转速度。
  spinY: 0,
  // 当前缩放。
  zoom: 1,
  // 目标缩放。
  zoomTarget: 1,
  // 缩放脉冲。
  zoomPulse: 0,
  // 是否正在拖拽。
  dragging: false,
  // 上一次指针 X。
  lastX: 0,
  // 上一次指针 Y。
  lastY: 0,
  // 上一次指针时间。
  lastT: 0,
  // 指针归一化 X。
  pointerX: 0.5,
  // 指针归一化 Y。
  pointerY: 0.5,
  // 指针是否活跃。
  pointerActive: false,
  // 指针聚焦强度。
  focus: 0,
  // 按压强度。
  press: 0,
  // 视差倾斜 X。
  tiltX: 0,
  // 视差倾斜 Y。
  tiltY: 0
};
// 设置待机引导可见状态和交互状态。
function setIdleGuideVisible(show, interactive) {
  document.body.classList.toggle('idle-guide-on', show);
  document.body.classList.toggle('idle-guide-interactive', !!interactive);
  if (!interactive) document.body.classList.remove('idle-guide-dragging');
  if (idleGuideVisible === show) return;
  idleGuideVisible = show;
}
// 判断当前是否应显示待机引导。
function shouldShowIdleGuide() {
  if (!IDLE_GUIDE_BACKGROUND_ENABLED) return false;
  if (immersiveMode) return false;
  if (playing) return false;
  if (document.querySelector('.modal-mask.show')) return false;
  if (uniforms && uniforms.uHasCover && uniforms.uHasCover.value > 0.5) return false;
  return true;
}
// 判断是否应显示歌单架悬停提示。
function shouldShowShelfHoverCue(value) {
  if (document.querySelector('.modal-mask.show')) return false;
  if (shelfPinnedOpen) return false;
  if (!shelfManager || !shelfManager.canInteract || !shelfManager.canInteract()) return false;
  if (shelfManager.hasOpenContent && shelfManager.hasOpenContent()) return false;
  if (!shelfManager.getMode || shelfManager.getMode() !== 'side') return false;
  return shelfHoverCue.target > 0 || (value || shelfHoverCue.value) > 0.015;
}
// 判断指针事件是否应交给待机引导处理。
function shouldHandleIdleGuidePointer(e) {
  if (!idleGuideCanvas || !shouldShowIdleGuide()) return false;
  if (isPointerOverUi(e)) return false;
  return true;
}
// 夹紧待机引导旋转速度。
function clampIdleGuideSpin(v) {
  if (!isFinite(v)) return 0;
  return Math.max(-4.8, Math.min(4.8, v));
}
// 待机引导指针按下处理。
function idleGuidePointerDown(e) {
  if (!shouldHandleIdleGuidePointer(e)) return;
  idleGuideInteraction.dragging = true;
  idleGuideInteraction.pointerActive = true;
  // 记录拖拽起点。
  idleGuideInteraction.lastX = e.clientX;
  idleGuideInteraction.lastY = e.clientY;
  idleGuideInteraction.lastT = performance.now();
  idleGuideInteraction.pointerX = e.clientX / Math.max(1, idleGuideW || innerWidth);
  idleGuideInteraction.pointerY = e.clientY / Math.max(1, idleGuideH || innerHeight);
  document.body.classList.add('idle-guide-dragging');
}
// 待机引导指针移动处理。
function idleGuidePointerMove(e) {
  if (!idleGuideCanvas) return;
  // 非拖拽时也允许指针悬停影响待机引导。
  var canReact = shouldHandleIdleGuidePointer(e) || idleGuideInteraction.dragging;
  idleGuideInteraction.pointerActive = canReact;
  if (canReact) {
    idleGuideInteraction.pointerX = e.clientX / Math.max(1, idleGuideW || innerWidth);
    idleGuideInteraction.pointerY = e.clientY / Math.max(1, idleGuideH || innerHeight);
  }
  if (!idleGuideInteraction.dragging) return;
  // 当前时间。
  var now = performance.now();
  // 帧间隔。
  var dt = Math.max(1 / 120, Math.min(0.08, (now - idleGuideInteraction.lastT) / 1000 || 1 / 60));
  // 指针 X 位移。
  var dx = e.clientX - idleGuideInteraction.lastX;
  // 指针 Y 位移。
  var dy = e.clientY - idleGuideInteraction.lastY;
  // X 轴旋转增量。
  var rx = -dy * 0.0032;
  // Y 轴旋转增量。
  var ry = dx * 0.0034;
  idleGuideInteraction.rotX += rx;
  idleGuideInteraction.rotY += ry;
  idleGuideInteraction.angle += ry * 0.22;
  idleGuideInteraction.spinX = clampIdleGuideSpin(rx / dt * 0.46);
  idleGuideInteraction.spinY = clampIdleGuideSpin(ry / dt * 0.46);
  idleGuideInteraction.velocity = Math.sqrt(idleGuideInteraction.spinX * idleGuideInteraction.spinX + idleGuideInteraction.spinY * idleGuideInteraction.spinY);
  idleGuideInteraction.lastX = e.clientX;
  idleGuideInteraction.lastY = e.clientY;
  idleGuideInteraction.lastT = now;
}
// 待机引导指针抬起处理。
function idleGuidePointerUp() {
  if (!idleGuideInteraction.dragging) return;
  idleGuideInteraction.dragging = false;
  document.body.classList.remove('idle-guide-dragging');
}
// 待机引导指针离开处理。
function idleGuidePointerLeave() {
  if (!idleGuideInteraction.dragging) idleGuideInteraction.pointerActive = false;
}
// 待机引导滚轮缩放处理。
function idleGuideWheel(e) {
  if (!shouldHandleIdleGuidePointer(e)) return false;
  // 交互状态引用。
  var guide = idleGuideInteraction;
  guide.pointerActive = true;
  guide.pointerX = e.clientX / Math.max(1, idleGuideW || innerWidth);
  guide.pointerY = e.clientY / Math.max(1, idleGuideH || innerHeight);
  // 目标缩放采用指数滚轮曲线。
  var nextZoom = guide.zoomTarget * Math.exp(-e.deltaY * 0.0012);
  guide.zoomTarget = Math.max(0.58, Math.min(1.82, nextZoom));
  guide.zoomPulse = Math.min(1, guide.zoomPulse + Math.min(0.28, Math.abs(e.deltaY) * 0.0014));
  return true;
}
// 调整待机引导 canvas 尺寸并重建粒子。
function resizeIdleGuideCanvas() {
  if (!idleGuideCanvas) return;
  // 限制 DPR，避免待机背景占用过高。
  idleGuideDpr = Math.min(window.devicePixelRatio || 1, 1.6);
  idleGuideW = window.innerWidth;
  idleGuideH = window.innerHeight;
  idleGuideCanvas.width = Math.max(1, Math.floor(idleGuideW * idleGuideDpr));
  idleGuideCanvas.height = Math.max(1, Math.floor(idleGuideH * idleGuideDpr));
  idleGuideCanvas.style.width = idleGuideW + 'px';
  idleGuideCanvas.style.height = idleGuideH + 'px';
  idleGuideCtx.setTransform(idleGuideDpr, 0, 0, idleGuideDpr, 0, 0);
  idleGuideParticles = [];
  resetIdleGuideTrails();
  if (!IDLE_GUIDE_BACKGROUND_ENABLED) return;
  // 视口短边。
  var minDim = Math.min(idleGuideW, idleGuideH);
  // 视口长边。
  var maxDim = Math.max(idleGuideW, idleGuideH);
  // 粒子数量。
  var count = idleGuideW < 800 ? 150 : 240;
  for (var i = 0; i < count; i++) {
    // 多数粒子分布在环形区域，少数作为远处漂浮层。
    var ring = i < count * 0.76;
    // 初始角度。
    var a = Math.random() * Math.PI * 2;
    // 半径。
    var r = ring
      ? (minDim * 0.035 + Math.pow(Math.random(), 0.58) * minDim * 0.335)
      : (Math.pow(Math.random(), 0.82) * maxDim * 0.58);
    // 摆动幅度。
    var wobbleAmp = minDim * (ring ? (0.012 + Math.random() * 0.035) : (0.010 + Math.random() * 0.055));
    idleGuideParticles.push({
      a: a,
      r: r,
      cx: ring ? 0.5 : Math.random(),
      cy: ring ? 0.5 : Math.random(),
      size: ring ? (0.30 + Math.random() * 0.62) : (0.18 + Math.random() * 0.44),
      speed: ((ring ? 0.018 : 0.010) + Math.random() * (ring ? 0.045 : 0.030)) * (Math.random() < 0.5 ? -1 : 1),
      phase: Math.random() * Math.PI * 2,
      wobbleAmp: wobbleAmp,
      wobbleSpeed: 0.18 + Math.random() * 0.76,
      oval: 0.56 + Math.random() * 0.36,
      zAmp: 0.34 + Math.random() * 0.82,
      driftX: (Math.random() * 2 - 1) * wobbleAmp * 0.75,
      driftY: (Math.random() * 2 - 1) * wobbleAmp * 0.75,
      layer: Math.random(),
      z: (Math.random() * 2 - 1) * (ring ? minDim * 0.28 : maxDim * 0.42),
      ring: ring
    });
  }
}
// 将待机引导 3D 点投影到 2D 屏幕。
function projectIdleGuidePoint(x, y, z, rot, cx, cy, depth) {
  // 绕 Y 轴旋转后的 X。
  var x1 = x * rot.cy + z * rot.sy;
  // 绕 Y 轴旋转后的 Z。
  var z1 = -x * rot.sy + z * rot.cy;
  // 绕 X 轴旋转后的 Y。
  var y1 = y * rot.cx - z1 * rot.sx;
  // 绕 X 轴旋转后的 Z。
  var z2 = y * rot.sx + z1 * rot.cx;
  // 透视缩放。
  var scale = depth / (depth - z2 * 0.72);
  scale = Math.max(0.52, Math.min(1.74, scale));
  return {
    x: cx + x1 * scale,
    y: cy + y1 * scale,
    z: z2,
    scale: scale
  };
}
// 重置待机引导拖尾数组。
function resetIdleGuideTrails() {
  idleGuideTrails = [[], [], [], []];
}
// 向指定待机引导拖尾写入一个点。
function pushIdleGuideTrail(index, pt, alpha, now) {
  // 目标拖尾数组。
  var trail = idleGuideTrails[index];
  if (!trail) trail = idleGuideTrails[index] = [];
  // 上一个拖尾点。
  var last = trail[trail.length - 1];
  // 与上一个点的 X 距离。
  var dx = last ? pt.x - last.x : 999;
  // 与上一个点的 Y 距离。
  var dy = last ? pt.y - last.y : 999;
  if (!last || Math.sqrt(dx * dx + dy * dy) > 1.4 || now - last.t > 42) {
    // 点间距或时间超过阈值时写入新拖尾点。
    trail.push({ x: pt.x, y: pt.y, scale: pt.scale || 1, alpha: alpha || 1, t: now });
  }
  // 限制单条拖尾长度。
  while (trail.length > 26) trail.shift();
}
// 绘制一条待机引导拖尾。
function drawIdleGuideTrail(ctx, trail, now, alpha, energy) {
  if (!trail || trail.length < 2) return;
  // 移除过旧的拖尾点。
  while (trail.length && now - trail[0].t > 680) trail.shift();
  if (trail.length < 2) return;
  ctx.save();
  ctx.lineCap = 'round';
  ctx.lineJoin = 'round';
  for (var i = 1; i < trail.length; i++) {
    // 上一个拖尾点。
    var prev = trail[i - 1];
    // 当前拖尾点。
    var cur = trail[i];
    // 当前点生命周期进度。
    var age = (now - cur.t) / 680;
    // 当前点在拖尾序列中的顺序权重。
    var order = i / Math.max(1, trail.length - 1);
    // 叠加年龄和顺序后的透明度。
    var fade = Math.max(0, 1 - age) * order;
    if (fade <= 0) continue;
    ctx.strokeStyle = 'rgba(255,255,255,' + (alpha * fade * (0.18 + energy * 0.24)).toFixed(3) + ')';
    ctx.lineWidth = (0.7 + cur.scale * 0.9 + energy * 1.2) * fade;
    ctx.beginPath();
    ctx.moveTo(prev.x, prev.y);
    // 二次贝塞尔中点。
    var mx = (prev.x + cur.x) * 0.5;
    // 二次贝塞尔中点 Y。
    var my = (prev.y + cur.y) * 0.5;
    ctx.quadraticCurveTo(mx, my, cur.x, cur.y);
    ctx.stroke();
  }
  ctx.restore();
}
// 调度下一帧待机引导绘制。
function scheduleIdleGuideFrame(delay) {
  if (idleGuideDelayTimer) {
    clearTimeout(idleGuideDelayTimer);
    idleGuideDelayTimer = null;
  }
  if (delay && delay > 0) {
    // 不需要高频刷新时延迟下一帧，降低待机成本。
    idleGuideDelayTimer = setTimeout(function(){
      idleGuideDelayTimer = null;
      requestAnimationFrame(drawIdleGuideFrame);
    }, delay);
  } else {
    requestAnimationFrame(drawIdleGuideFrame);
  }
}
// 绘制待机引导和歌单架边缘提示。
function drawIdleGuideFrame() {
  if (!idleGuideCanvas || !idleGuideCtx) return;
  // 画布上下文。
  var ctx = idleGuideCtx;
  // 当前帧时间。
  var nowFrame = performance.now();
  // 帧间隔秒数。
  var dtFrame = Math.max(1 / 120, Math.min(0.05, (nowFrame - idleGuideLastFrameAt) / 1000 || 1 / 60));
  idleGuideLastFrameAt = nowFrame;
  // 是否显示待机背景。
  var idleShow = shouldShowIdleGuide();
  // 歌单架悬停提示强度。
  var shelfCueValue = tickShelfHoverCue(dtFrame);
  // 是否显示歌单架提示。
  var shelfCueShow = shouldShowShelfHoverCue(shelfCueValue);
  // 本帧是否需要显示任何待机画面。
  var show = idleShow || shelfCueShow;
  setIdleGuideVisible(show, idleShow);
  if (!show) {
    // 完全隐藏时清空画布并低频轮询。
    idleGuideCtx.clearRect(0, 0, idleGuideW, idleGuideH);
    resetIdleGuideTrails();
    scheduleIdleGuideFrame(140);
    return;
  }
  // 待机引导运行秒数。
  var t = (nowFrame - idleGuideStartedAt) / 1000;
  if (!idleShow) {
    // 不显示待机背景时，仅绘制歌单架提示。
    ctx.clearRect(0, 0, idleGuideW, idleGuideH);
    resetIdleGuideTrails();
    ctx.globalCompositeOperation = 'lighter';
    drawShelfGuideCue(ctx, t, shelfCueValue);
    ctx.globalCompositeOperation = 'source-over';
    scheduleIdleGuideFrame(0);
    return;
  }
  // 画布中心 X。
  var cx = idleGuideW * 0.5;
  // 画布中心 Y。
  var cy = idleGuideH * 0.50;
  // 交互状态引用。
  var guide = idleGuideInteraction;
  if (!guide.dragging) {
    // 非拖拽状态下应用惯性旋转和阻尼。
    guide.rotX += guide.spinX * dtFrame;
    guide.rotY += guide.spinY * dtFrame;
    guide.spinX *= Math.pow(0.90, dtFrame * 60);
    guide.spinY *= Math.pow(0.90, dtFrame * 60);
    if (Math.abs(guide.spinX) < 0.01) guide.spinX = 0;
    if (Math.abs(guide.spinY) < 0.01) guide.spinY = 0;
  }
  guide.rotY += 0.012 * dtFrame;
  guide.angle += guide.spinY * dtFrame * 0.20 + 0.010 * dtFrame;
  guide.velocity = Math.sqrt(guide.spinX * guide.spinX + guide.spinY * guide.spinY);
  // 指针目标聚焦值。
  var targetFocus = guide.pointerActive ? 1 : 0;
  // 拖拽目标按压值。
  var targetPress = guide.dragging ? 1 : 0;
  guide.focus += (targetFocus - guide.focus) * 0.10;
  guide.press += (targetPress - guide.press) * 0.16;
  guide.zoom += (guide.zoomTarget - guide.zoom) * 0.13;
  guide.zoomPulse *= Math.pow(0.84, dtFrame * 60);
  if (guide.zoomPulse < 0.002) guide.zoomPulse = 0;
  guide.tiltX += (((guide.pointerX - 0.5) * 0.26) - guide.tiltX) * 0.08;
  guide.tiltY += (((guide.pointerY - 0.5) * 0.18) - guide.tiltY) * 0.08;
  ctx.clearRect(0, 0, idleGuideW, idleGuideH);
  ctx.globalCompositeOperation = 'lighter';

  // 呼吸动画强度。
  var breathe = 0.5 + 0.5 * Math.sin(t * 0.72);
  // 当前缩放。
  var zoom = guide.zoom;
  // 滚轮缩放脉冲。
  var zoomBoost = guide.zoomPulse;
  // 背景中心光晕。
  var halo = ctx.createRadialGradient(cx, cy, 0, cx, cy, Math.min(idleGuideW, idleGuideH) * ((0.36 + breathe * 0.035 + guide.press * 0.018) * zoom));
  halo.addColorStop(0, 'rgba(255,255,255,' + (0.034 + breathe * 0.020 + guide.focus * 0.014 + guide.press * 0.018 + zoomBoost * 0.018).toFixed(3) + ')');
  halo.addColorStop(0.44, 'rgba(255,255,255,' + (0.014 + guide.focus * 0.010).toFixed(3) + ')');
  halo.addColorStop(1, 'rgba(255,255,255,0)');
  ctx.fillStyle = halo;
  ctx.fillRect(0, 0, idleGuideW, idleGuideH);

  // 环形粒子投影点列表，后续用于连线。
  var ringPts = [];
  // 指针屏幕 X。
  var pointerX = guide.pointerX * idleGuideW;
  // 指针屏幕 Y。
  var pointerY = guide.pointerY * idleGuideH;
  // 拖拽/惯性带来的能量。
  var spinEnergy = Math.min(1, guide.velocity / 1.5 + guide.press * 0.42);
  // 当前旋转三角函数缓存。
  var rot = {
    sx: Math.sin(guide.rotX),
    cx: Math.cos(guide.rotX),
    sy: Math.sin(guide.rotY),
    cy: Math.cos(guide.rotY)
  };
  // 透视深度基准。
  var depth = Math.max(520, Math.min(idleGuideW, idleGuideH) * 0.92);
  for (var i = 0; i < idleGuideParticles.length; i++) {
    // 当前粒子。
    var p = idleGuideParticles[i];
    // 粒子当前角度。
    var localA = p.a + t * p.speed;
    // 粒子摆动相位。
    var wanderA = p.phase + t * p.wobbleSpeed;
    // 粒子摆动位移。
    var wobble = Math.sin(wanderA) * p.wobbleAmp + Math.sin(t * (p.wobbleSpeed * 0.57 + 0.11) + p.phase * 1.7) * p.wobbleAmp * 0.45;
    // 粒子屏幕 X/Y。
    var x, y;
    // 3D 投影结果。
    var projected = null;
    // 点大小缩放。
    var pointScale = 1;
    if (p.ring) {
      // 环形粒子在 3D 环上运动。
      var rr = (p.r + wobble + breathe * 12) * zoom * (1 + guide.press * 0.030 + zoomBoost * 0.018);
      var baseX = Math.cos(localA) * rr + Math.sin(wanderA * 0.73) * p.wobbleAmp * 0.54 + p.driftX;
      var baseY = Math.sin(localA + Math.sin(wanderA) * 0.10) * rr * p.oval + Math.sin(t * 0.33 + p.phase) * p.wobbleAmp * 0.68 + p.driftY;
      var baseZ = (Math.sin(localA * 0.84 + p.phase * 0.31) * rr * p.zAmp + p.z * 0.54 + Math.cos(wanderA * 0.91) * p.wobbleAmp) * zoom;
      projected = projectIdleGuidePoint(baseX, baseY, baseZ, rot, cx, cy, depth);
      pointScale = projected.scale;
      x = projected.x + guide.tiltX * projected.z * 0.020;
      y = projected.y + guide.tiltY * projected.z * 0.018;
      var nDx = pointerX - x, nDy = pointerY - y;
      var near = guide.focus * Math.max(0, 1 - Math.sqrt(nDx * nDx + nDy * nDy) / 210);
      x += nDx * near * 0.040;
      y += nDy * near * 0.040;
      ringPts.push({ x:x, y:y, z:projected.z, scale:projected.scale, alpha:0.08 + breathe * 0.04 + near * 0.08 });
    } else {
      // 远场粒子在更大的空间里漂移。
      var driftX = ((p.cx - 0.5) * idleGuideW * 0.92 + Math.cos(localA) * (12 + p.wobbleAmp * 0.28) + wobble * 0.28) * zoom;
      var driftY = ((p.cy - 0.5) * idleGuideH * 0.72 + Math.sin(localA * 0.8 + p.phase * 0.2) * (12 + p.wobbleAmp * 0.24)) * zoom;
      var driftZ = (p.z + Math.sin(localA + p.phase) * (32 + p.wobbleAmp * 0.32)) * zoom;
      var fieldPt = projectIdleGuidePoint(driftX, driftY, driftZ, rot, cx, cy, depth * 1.16);
      pointScale = fieldPt.scale;
      x = fieldPt.x;
      y = fieldPt.y;
    }
    // 深度影响光点透明度。
    var depthGlow = p.ring && projected ? (0.66 + projected.scale * 0.20) : 1;
    // 粒子透明度。
    var aP = p.ring ? ((0.070 + breathe * 0.065 + Math.sin(t * (0.8 + p.layer) + p.phase) * 0.024 + spinEnergy * 0.032) * depthGlow) : (0.034 + guide.focus * 0.010);
    ctx.beginPath();
    ctx.arc(x, y, p.size * pointScale * Math.sqrt(zoom) * (1 + spinEnergy * (p.ring ? 0.24 : 0.08) + zoomBoost * 0.12), 0, Math.PI * 2);
    ctx.fillStyle = 'rgba(255,255,255,' + Math.max(0, aP).toFixed(3) + ')';
    ctx.fill();
  }

  ctx.lineWidth = 1;
  for (var j = 0; j < ringPts.length; j += 3) {
    // 连线起点。
    var aPt = ringPts[j];
    // 连线终点。
    var bPt = ringPts[(j + 7) % ringPts.length];
    if (!aPt || !bPt) continue;
    // 点间距离。
    var dx = aPt.x - bPt.x, dy = aPt.y - bPt.y;
    var dist = Math.sqrt(dx * dx + dy * dy);
    if (dist > Math.min(idleGuideW, idleGuideH) * 0.17) continue;
    ctx.strokeStyle = 'rgba(255,255,255,' + (0.018 + breathe * 0.020 + guide.focus * 0.012 + spinEnergy * 0.018).toFixed(3) + ')';
    ctx.beginPath();
    ctx.moveTo(aPt.x, aPt.y);
    ctx.lineTo(bPt.x, bPt.y);
    ctx.stroke();
  }

  if (guide.focus > 0.03 || spinEnergy > 0.05) {
    // 交互锚点轨道半径。
    var orbitR = Math.min(idleGuideW, idleGuideH) * (0.305 + guide.press * 0.018) * zoom;
    // 锚点透明度。
    var anchorAlpha = Math.min(0.68, 0.16 + guide.focus * 0.24 + spinEnergy * 0.38);
    for (var k = 0; k < 4; k++) {
      // 锚点角度。
      var anchorA = guide.angle + t * 0.08 + k * 1.72 + (k === 2 ? 0.38 : 0);
      // 锚点投影位置。
      var anchorPt = projectIdleGuidePoint(
        Math.cos(anchorA) * orbitR,
        Math.sin(anchorA) * orbitR * 0.52,
        Math.sin(anchorA + k * 0.54) * orbitR * 0.48,
        rot, cx, cy, depth
      );
      pushIdleGuideTrail(k, anchorPt, anchorAlpha, nowFrame);
      drawIdleGuideTrail(ctx, idleGuideTrails[k], nowFrame, anchorAlpha, spinEnergy);
      ctx.beginPath();
      ctx.arc(anchorPt.x, anchorPt.y, (2.0 + spinEnergy * 1.8 + (k === 0 ? guide.press * 1.8 : 0)) * anchorPt.scale, 0, Math.PI * 2);
      ctx.fillStyle = 'rgba(255,255,255,' + anchorAlpha.toFixed(3) + ')';
      ctx.fill();
    }
  }

  if (guide.focus > 0.03) {
    // 指针交互手柄角度。
    var handleA = guide.angle + t * 0.36;
    // 指针交互手柄半径。
    var handleR = Math.min(idleGuideW, idleGuideH) * (0.315 + breathe * 0.012 + guide.press * 0.012) * zoom;
    // 手柄投影位置。
    var handlePt = projectIdleGuidePoint(
      Math.cos(handleA) * handleR,
      Math.sin(handleA) * handleR * 0.52,
      Math.sin(handleA + 0.62) * handleR * 0.48,
      rot, cx, cy, depth
    );
    // 手柄屏幕 X。
    var hx = handlePt.x;
    // 手柄屏幕 Y。
    var hy = handlePt.y;
    // 手柄光晕。
    var handleGlow = ctx.createRadialGradient(hx, hy, 0, hx, hy, 28 + guide.press * 12);
    handleGlow.addColorStop(0, 'rgba(255,255,255,' + (0.22 * guide.focus + 0.16 * guide.press).toFixed(3) + ')');
    handleGlow.addColorStop(1, 'rgba(255,255,255,0)');
    ctx.fillStyle = handleGlow;
    ctx.beginPath();
    ctx.arc(hx, hy, 28 + guide.press * 12, 0, Math.PI * 2);
    ctx.fill();
    ctx.beginPath();
    ctx.arc(hx, hy, 2.4 + guide.press * 1.6, 0, Math.PI * 2);
    ctx.fillStyle = 'rgba(255,255,255,' + (0.54 * guide.focus + 0.24 * guide.press).toFixed(3) + ')';
    ctx.fill();
  }

  // 有歌单架提示时叠加边缘提示。
  if (shelfCueShow) drawShelfGuideCue(ctx, t, shelfCueValue);
  ctx.globalCompositeOperation = 'source-over';
  scheduleIdleGuideFrame(0);
}
// 绘制圆角矩形路径，兼容不支持 roundRect 的环境。
function idleRoundRect(ctx, x, y, w, h, r) {
  if (ctx.roundRect) {
    ctx.roundRect(x, y, w, h, r);
    return;
  }
  // 限制圆角半径不超过宽高一半。
  r = Math.min(r || 0, Math.abs(w) * 0.5, Math.abs(h) * 0.5);
  // 右下角坐标。
  var x2 = x + w, y2 = y + h;
  ctx.moveTo(x + r, y);
  ctx.lineTo(x2 - r, y);
  ctx.quadraticCurveTo(x2, y, x2, y + r);
  ctx.lineTo(x2, y2 - r);
  ctx.quadraticCurveTo(x2, y2, x2 - r, y2);
  ctx.lineTo(x + r, y2);
  ctx.quadraticCurveTo(x, y2, x, y2 - r);
  ctx.lineTo(x, y + r);
  ctx.quadraticCurveTo(x, y, x + r, y);
}
// 绘制歌单架侧边悬停提示。
function drawShelfGuideCue(ctx, t, strength) {
  strength = Math.max(0, Math.min(1, strength == null ? shelfHoverCue.value : strength));
  if (strength <= 0.01) return;
  // 提示热区矩形。
  var r = shelfCueRect();
  // 提示中心点。
  var c = shelfCueCenter();
  // 呼吸脉冲。
  var pulse = 0.5 + 0.5 * Math.sin(t * 1.55);
  // 提示整体上下浮动。
  var floatY = Math.sin(t * 0.92) * 8 * strength;

  ctx.save();
  ctx.globalCompositeOperation = 'lighter';
  // 右侧边缘线性辉光。
  var glow = ctx.createLinearGradient(r.left, 0, r.right, 0);
  glow.addColorStop(0, 'rgba(255,255,255,0)');
  glow.addColorStop(0.58, 'rgba(255,255,255,' + (0.010 * strength).toFixed(3) + ')');
  glow.addColorStop(0.82, 'rgba(244,210,138,' + (0.024 * strength + pulse * 0.012 * strength).toFixed(3) + ')');
  glow.addColorStop(1, 'rgba(255,255,255,' + (0.035 * strength).toFixed(3) + ')');
  ctx.fillStyle = glow;
  ctx.fillRect(r.left, r.top - 26, r.width + 18, r.height + 52);

  // 提示中心径向光晕。
  var halo = ctx.createRadialGradient(c.x + r.width * 0.18, c.y + floatY, 0, c.x + r.width * 0.18, c.y + floatY, r.width * 0.62);
  halo.addColorStop(0, 'rgba(244,210,138,' + (0.070 * strength + pulse * 0.026 * strength).toFixed(3) + ')');
  halo.addColorStop(0.45, 'rgba(255,255,255,' + (0.020 * strength).toFixed(3) + ')');
  halo.addColorStop(1, 'rgba(255,255,255,0)');
  ctx.fillStyle = halo;
  ctx.fillRect(r.left, r.top - 40, r.width, r.height + 80);

  for (var i = 0; i < 10; i++) {
    // 粒子随机种子。
    var seed = i * 19.17;
    // 粒子闪烁相位。
    var phase = (t * (0.10 + (i % 4) * 0.014) + i * 0.113) % 1;
    // 粒子 X 坐标。
    var x = r.left + r.width * (0.45 + (i % 4) * 0.13) + Math.sin(t * 0.44 + seed) * 12;
    // 粒子 Y 坐标。
    var y = r.top + r.height * (0.18 + ((i * 0.137 + Math.sin(seed)) % 0.64)) + floatY * (0.42 + (i % 3) * 0.10);
    // 粒子透明度。
    var alpha = (0.035 + Math.sin(Math.PI * phase) * 0.050) * strength;
    if (alpha <= 0) continue;
    ctx.beginPath();
    ctx.arc(x, y, 0.9 + (i % 3) * 0.26 + pulse * 0.18, 0, Math.PI * 2);
    ctx.fillStyle = 'rgba(244,210,138,' + alpha.toFixed(3) + ')';
    ctx.fill();
  }
  ctx.restore();
}
// 初始化待机引导 canvas 和绘制循环。
function initIdleGuideCanvas() {
  idleGuideCanvas = document.getElementById('idle-guide-canvas');
  if (!idleGuideCanvas) return;
  idleGuideCtx = idleGuideCanvas.getContext('2d');
  if (!idleGuideCtx) return;
  idleGuideStartedAt = performance.now();
  resizeIdleGuideCanvas();
  window.addEventListener('resize', resizeIdleGuideCanvas);
  drawIdleGuideFrame();
}

// ============================================================
//  toast
// ============================================================
// toast 自动关闭定时器。
var toastTimer = null;
// 显示底部 toast 提示。
function showToast(msg) {
  // toast 节点。
  var t = document.getElementById('toast');
  t.textContent = msg;
  t.classList.add('show');
  if (toastTimer) clearTimeout(toastTimer);
  toastTimer = setTimeout(function(){ t.classList.remove('show'); }, 2600);
}

// ===== js/10-device-bootstrap.js =====

// ============================================================
//  粒子鼠标拖拽旋转
// ============================================================
// 物理旋转: 给粒子一个角速度, 每帧衰减
var particleSpin = { vx: 0, vy: 0, damping: 0.90 };
// 鼠标拖拽驱动的总旋转累计角度
var particleRotation = { x: 0, y: 0 };
// 指针 Y 位移转 X 轴旋转的系数。
var PARTICLE_POINTER_SPIN_X = 0.0032;
// 指针 X 位移转 Y 轴旋转的系数。
var PARTICLE_POINTER_SPIN_Y = 0.0034;
// 粒子惯性旋转最大角速度。
var PARTICLE_SPIN_MAX = 6.2;

// 夹紧粒子惯性旋转速度。
function clampParticleSpinVelocity(v) {
  if (!isFinite(v)) return 0;
  return Math.max(-PARTICLE_SPIN_MAX, Math.min(PARTICLE_SPIN_MAX, v));
}

// 将一次拖拽位移应用到粒子旋转目标和惯性速度。
function applyParticleSpinDrag(dx, dy, dt) {
  // X 轴旋转增量。
  var rx = dy * PARTICLE_POINTER_SPIN_X;
  // Y 轴旋转增量。
  var ry = dx * PARTICLE_POINTER_SPIN_Y;
  particleRotation.x += rx;
  particleRotation.y += ry;
  if (dt > 0) {
    // 根据时间差换算惯性角速度。
    particleSpin.vx = clampParticleSpinVelocity(rx / dt * 0.46);
    particleSpin.vy = clampParticleSpinVelocity(ry / dt * 0.46);
  }
}

function resetParticleRotationTarget(syncVisual) {
  // 恢复粒子旋转目标时同步清零惯性速度；必要时也把所有可视层的当前旋转立即对齐。
  particleRotation.x = 0;
  particleRotation.y = 0;
  particleSpin.vx = 0;
  particleSpin.vy = 0;
  if (syncVisual && particles) {
    particles.rotation.set(0, 0, 0);
    if (bloomParticles) bloomParticles.rotation.set(0, 0, 0);
    if (floatGroup) floatGroup.rotation.set(0, 0, 0);
    if (backCoverGroup) backCoverGroup.rotation.set(0, 0, 0);
  }
}

function rebaseParticleRotationAxis(axis) {
  // 长时间拖拽或惯性旋转会让角度持续增长，定期按 2π 回基，避免浮点误差影响插值和射线命中。
  var limit = Math.PI * 10;
  if (Math.abs(particleRotation[axis]) < limit) return;
  var offset = Math.round(particleRotation[axis] / (Math.PI * 2)) * Math.PI * 2;
  particleRotation[axis] -= offset;
  if (particles) particles.rotation[axis] -= offset;
  if (bloomParticles) bloomParticles.rotation[axis] -= offset;
  if (floatGroup) floatGroup.rotation[axis] -= offset;
  if (backCoverGroup) backCoverGroup.rotation[axis] -= offset;
  if (skullParticleGroup) skullParticleGroup.rotation[axis] -= offset;
  if (stageLyrics.group) stageLyrics.group.rotation[axis] -= offset;
}

function rebaseParticleRotationIfNeeded() {
  rebaseParticleRotationAxis('x');
  rebaseParticleRotationAxis('y');
}

// 每帧推进粒子拖拽惯性。
function tickParticleSpin(dt) {
  // 松手后的粒子惯性在这里按帧衰减，粒子、辉光层、浮空层和背面封面层会在主循环里同步到同一旋转。
  if (Math.abs(particleSpin.vx) > 0.0001 || Math.abs(particleSpin.vy) > 0.0001) {
    // 本帧 X 轴旋转增量。
    var rx = particleSpin.vx * dt;
    // 本帧 Y 轴旋转增量。
    var ry = particleSpin.vy * dt;
    particleRotation.x += rx;
    particleRotation.y += ry;
    rebaseParticleRotationIfNeeded();
  }
  particleSpin.vx *= Math.pow(particleSpin.damping, dt * 60);
  particleSpin.vy *= Math.pow(particleSpin.damping, dt * 60);
  if (Math.abs(particleSpin.vx) < 0.01) particleSpin.vx = 0;
  if (Math.abs(particleSpin.vy) < 0.01) particleSpin.vy = 0;
}


// ============================================================
//  Resize / 快捷键
// ============================================================
// 刷新主渲染器视口和相机投影。
function refreshMainRendererViewport(reason) {
  // 视口刷新只处理主相机和渲染功耗；歌词相机在全屏下额外请求多帧校准以避开宿主窗口尺寸抖动。
  if (typeof camera !== 'undefined' && camera) {
    camera.aspect = Math.max(1, innerWidth) / Math.max(1, innerHeight);
    camera.updateProjectionMatrix();
  }
  applyRendererPowerMode();
  if (typeof requestStageLyricCameraSnap === 'function' && desktopRuntimeState.fullscreen) {
    requestStageLyricCameraSnap(reason === 'resize' ? 4 : 10);
  }
}
// 排队多次刷新主渲染视口，用于覆盖宿主窗口动画和 DPI 延迟。
function scheduleMainRendererViewportRefresh(reason) {
  // resize 后连续排几次刷新，覆盖桌面宿主窗口动画、DPI 变化和 iframe 尺寸延迟更新。
  refreshMainRendererViewport(reason || 'sync');
  [48, 140, 320].forEach(function(delay){
    setTimeout(function(){ refreshMainRendererViewport(reason || 'sync'); }, delay);
  });
}
// 浏览器窗口尺寸变化时刷新渲染视口。
window.addEventListener('resize', function(){
  scheduleMainRendererViewportRefresh('resize');
});
// 全局播放快捷键。
document.addEventListener('keydown', function(e){
  if (isTypingTarget(e.target)) return;
  if (e.code === 'Space') {
    // 空格切换播放；自由相机使用空格时不触发播放。
    if (freeCamera && freeCamera.active) { e.preventDefault(); return; }
    e.preventDefault(); togglePlay();
  }
  else if (e.code === 'ArrowUp') { e.preventDefault(); adjustVolumeByKeyboard(0.05); }
  else if (e.code === 'ArrowDown') { e.preventDefault(); adjustVolumeByKeyboard(-0.05); }
  else if (e.code === 'ArrowRight') nextTrack();
  else if (e.code === 'ArrowLeft')  prevTrack();
  else if (e.code === 'Escape')     {
    if (immersiveMode) {
      e.preventDefault();
      setImmersiveMode(false);
      return;
    }
    if (miniQueueOpen) { closeMiniQueue(); return; }
    if (shelfManager && shelfManager.hasOpenContent()) { safeShelfCloseContent('escape-key'); return; }
    togglePlaylistPanel(false);
  }
  else if (e.code === 'KeyL') { if (!immersiveMode) toggleLyricsPanel(); }
  else if (e.code === 'KeyI') toggleImmersiveMode();
  else if (e.code === 'KeyF') toggleFullscreen();
});

// ============================================================
//  UI 半隐藏 v8 — 面板触发/隐藏体验统一
//   - 控制台 (右侧): x > w-48 进入, x < w-380 离开
//   - 队列 (左侧): x < 48 进入, x > 380 离开
//   - 进入立即显示, 离开延迟 500ms (统一)
// ============================================================
// 半隐藏面板离开后的隐藏延迟。
var PEEK_HIDE_DELAY = 170;
// 控制台和队列面板的 peek 隐藏定时器。
var peekTimers = { fx:null, pl:null };
// 设置面板 peek 半展开状态。
function setPeek(el, on, key) {
  if (!el) return;
  if (!on && key === 'pl' && playlistPanelPinned) return;
  if (on) {
    // 进入前是否已经是 peek 状态。
    var wasPeek = el.classList.contains('peek');
    if (peekTimers[key]) { clearTimeout(peekTimers[key]); peekTimers[key] = null; }
    if (key === 'fx') el.classList.remove('closing');
    if (key === 'pl' && !wasPeek && !playQueue.length && queueViewTab === 'queue') switchPlaylistTab('playlists');
    if (key === 'pl' && !wasPeek && playQueue.length && currentIdx >= 0) {
      // 左侧队列打开时优先切回队列并滚到当前歌曲。
      if (el.dataset && el.dataset.preserveTabOnOpen === '1') delete el.dataset.preserveTabOnOpen;
      else if (queueViewTab !== 'queue') switchPlaylistTab('queue');
      scrollPlaylistPanelToCurrent();
    } else if (key === 'pl' && el.dataset && el.dataset.preserveTabOnOpen === '1') {
      delete el.dataset.preserveTabOnOpen;
    }
    el.classList.add('peek');
    if (key === 'pl' && !wasPeek) {
      // 队列首次 peek 时刷新延迟渲染内容。
      scheduleUiWarmTask(function(){
        flushDeferredQueuePanel('playlist-panel-peek');
        if (queueViewTab === 'queue') animateVisiblePanelList(document.getElementById('queue-list'), '.queue-item', el, '.queue-item.now', { scrollActive: false });
      }, 180);
    }
    if (key === 'fx') {
      // 控制台 peek 时同步悬浮按钮。
      var fabOn = document.getElementById('fx-fab');
      if (fabOn) fabOn.classList.add('active');
    }
  } else {
    // 关闭使用延迟，避免指针跨边界时闪烁。
    if (peekTimers[key]) clearTimeout(peekTimers[key]);
    peekTimers[key] = setTimeout(function(){
      el.classList.remove('peek');
      if (key === 'fx') {
        var fabOff = document.getElementById('fx-fab');
        if (fabOff && !el.classList.contains('show')) fabOff.classList.remove('active');
      }
      peekTimers[key] = null;
    }, PEEK_HIDE_DELAY);
  }
}
// 二级屏左边缘队列触发保护状态。
var secondaryPlaylistEdgeGuard = { enteredAt:0, timer:null, x:0, y:0, H:0 };
// 二级屏左边缘安全带最小 X。
var SECONDARY_PLAYLIST_EDGE_MIN_X = 36;
// 二级屏左边缘安全带最大 X。
var SECONDARY_PLAYLIST_EDGE_MAX_X = 96;
// 二级屏左边缘停留触发时长。
var SECONDARY_PLAYLIST_EDGE_DWELL_MS = 220;
// 二级屏拼接缝关闭阈值。
var SECONDARY_PLAYLIST_SEAM_CLOSE_X = 28;
// 判断二级左屏拼接缝保护是否启用；当前关闭。
function isSecondaryLeftDisplaySeamGuardActive() {
  return false;
}
// 重置二级屏边缘触发保护状态。
function resetSecondaryPlaylistEdgeGuard() {
  if (secondaryPlaylistEdgeGuard.timer) {
    clearTimeout(secondaryPlaylistEdgeGuard.timer);
    secondaryPlaylistEdgeGuard.timer = null;
  }
  secondaryPlaylistEdgeGuard.enteredAt = 0;
}
// 判断指针是否在二级屏左边缘安全带内。
function isSecondaryPlaylistSafeBandPoint(ex, ey, H) {
  return ey > 132 && ey < H - 132 && ex >= SECONDARY_PLAYLIST_EDGE_MIN_X && ex < SECONDARY_PLAYLIST_EDGE_MAX_X;
}
// 启动二级屏边缘停留计时。
function armSecondaryPlaylistEdgeDwell() {
  if (secondaryPlaylistEdgeGuard.timer) return;
  secondaryPlaylistEdgeGuard.timer = setTimeout(function(){
    secondaryPlaylistEdgeGuard.timer = null;
    if (!isSecondaryLeftDisplaySeamGuardActive()) return;
    if (!isSecondaryPlaylistSafeBandPoint(secondaryPlaylistEdgeGuard.x, secondaryPlaylistEdgeGuard.y, secondaryPlaylistEdgeGuard.H)) return;
    var panel = document.getElementById('playlist-panel');
    if (panel) setPeek(panel, true, 'pl');
  }, SECONDARY_PLAYLIST_EDGE_DWELL_MS);
}
// 判断当前位置是否触发左侧播放队列边缘区域。
function isPlaylistEdgeTrigger(ex, ey, H) {
  // 垂直安全区域。
  var inVerticalBand = ey > 132 && ey < H - 132;
  if (!inVerticalBand) {
    resetSecondaryPlaylistEdgeGuard();
    return false;
  }
  if (!isSecondaryLeftDisplaySeamGuardActive()) {
    return ex >= 14 && ex < 78;
  }
  // 二级屏保护模式下需要在安全带停留。
  var inSafeBand = isSecondaryPlaylistSafeBandPoint(ex, ey, H);
  if (!inSafeBand) {
    resetSecondaryPlaylistEdgeGuard();
    return false;
  }
  secondaryPlaylistEdgeGuard.x = ex;
  secondaryPlaylistEdgeGuard.y = ey;
  secondaryPlaylistEdgeGuard.H = H;
  // 当前时间。
  var now = performance.now();
  if (!secondaryPlaylistEdgeGuard.enteredAt) secondaryPlaylistEdgeGuard.enteredAt = now;
  armSecondaryPlaylistEdgeDwell();
  return now - secondaryPlaylistEdgeGuard.enteredAt >= SECONDARY_PLAYLIST_EDGE_DWELL_MS;
}
// 左侧队列面板退出判定的额外右侧 padding。
function playlistPanelExitPadding() {
  return isSecondaryLeftDisplaySeamGuardActive() ? 34 : 72;
}
// 左侧队列面板焦点判定 padding。
function playlistPanelFocusPadding() {
  return isSecondaryLeftDisplaySeamGuardActive() ? 28 : 52;
}
// 判断指针是否已离开到应关闭队列面板的位置。
function shouldClosePlaylistPanelFromPointer(ppOn, ex, ppRect) {
  if (!ppOn) return false;
  if (isSecondaryLeftDisplaySeamGuardActive() && ex < SECONDARY_PLAYLIST_SEAM_CLOSE_X) return true;
  return ex > ppRect.right + playlistPanelExitPadding();
}
// 判断队列面板焦点是否应保持。
function isPlaylistPanelFocusActive(inTrigger, inPanel, pp, ex, ppRect) {
  if (isSecondaryLeftDisplaySeamGuardActive() && ex < SECONDARY_PLAYLIST_SEAM_CLOSE_X) return false;
  return inTrigger || inPanel || (pp && pp.classList.contains('peek') && ex < ppRect.right + playlistPanelFocusPadding());
}
// 全局鼠标移动负责面板 peek、歌单架 hover 和焦点区切换。
window.addEventListener('mousemove', function(e){
  // 视觉控制台面板。
  var fp = document.getElementById('fx-panel');
  // 播放列表面板。
  var pp = document.getElementById('playlist-panel');
  // 指针坐标和视口尺寸。
  var ex = e.clientX, ey = e.clientY, W = innerWidth, H = innerHeight;
  if (immersiveMode) {
    // 沉浸模式下只保留必要面板和焦点交互。
    updateShelfHoverCueFromPointer(e);
    updateShelfCardHoverSelection(e);
    updateControlsAutoHideFromPointer(ex, ey);
    // 队列面板是否处于 peek。
    var ppOnImm = pp.classList.contains('peek');
    // 队列面板矩形。
    var ppRectImm = pp.getBoundingClientRect();
    // 沉浸模式不使用左边缘自动触发。
    var inQueueTriggerImm = false;
    // 指针是否在队列面板附近。
    var inQueuePanelImm = ppOnImm && ex >= ppRectImm.left - 18 && ex <= ppRectImm.right + 24 && ey >= ppRectImm.top - 22 && ey <= ppRectImm.bottom + 22;
    if (inQueuePanelImm) setPeek(pp, true, 'pl');
    else if (shouldClosePlaylistPanelFromPointer(ppOnImm, ex, ppRectImm)) setPeek(pp, false, 'pl');
    // 歌单架是否可成为焦点。
    var shelfCanFocusImm = !!(shelfManager && shelfManager.canInteract && shelfManager.canInteract());
    // 新焦点区。
    var newFocusImm = null;
    // 队列焦点状态。
    var queueFocusImm = isPlaylistPanelFocusActive(inQueueTriggerImm, inQueuePanelImm, pp, ex, ppRectImm);
    // 侧边歌单架 hover 焦点。
    var shelfHoverFocusImm = !!(shelfCanFocusImm && isSideShelfFocusHit(e));
    if (queueFocusImm) newFocusImm = 'queue';
    else if (shelfManager && shelfManager.hasOpenContent && shelfManager.hasOpenContent()) newFocusImm = 'shelf-detail';
    else if (shelfHoverFocusImm) newFocusImm = 'shelf-side';
    else if (shelfCanFocusImm && shelfManager.getMode() === 'stage' && ey > H * 0.55) newFocusImm = 'shelf-stage';
    setFocusZone(newFocusImm, newFocusImm === 'queue');
    return;
  }
  updateShelfHoverCueFromPointer(e);
  updateShelfCardHoverSelection(e);
  // 视觉控制台只由右下角按钮展开，由标题栏关闭按钮关闭。
  // 播放队列 DOM 面板不再由左侧边缘自动弹出，仅保留已打开后的悬停保持
  // 队列面板是否处于 peek。
  var ppOn = pp.classList.contains('peek');
  // 队列面板矩形。
  var ppRect = pp.getBoundingClientRect();
  // 普通模式也不再使用左边缘自动触发。
  var inQueueTrigger = false;
  // 指针是否在队列面板附近。
  var inQueuePanel = ppOn && ex >= ppRect.left - 18 && ex <= ppRect.right + 24 && ey >= ppRect.top - 22 && ey <= ppRect.bottom + 22;
  if (inQueuePanel) setPeek(pp, true, 'pl');
  else if (shouldClosePlaylistPanelFromPointer(ppOn, ex, ppRect)) setPeek(pp, false, 'pl');

  // v8: 镜头跟拍触发判断
  //   - 队列面板 peek 时 → queue focus
  //   - 3D shelf side 模式只在点击展开后 → shelf-side
  //   - 3D shelf stage 模式 + 鼠标在下 35% → shelf-stage
  // 歌单架是否可成为焦点。
  var shelfCanFocus = !!(shelfManager && shelfManager.canInteract && shelfManager.canInteract());
  if (!shelfCanFocus && !(shelfManager && shelfManager.hasOpenContent && shelfManager.hasOpenContent())) {
    shelfPinnedOpen = false;
  }

  // 新焦点区。
  var newFocus = null;
  // 队列焦点是否活跃。
  var queueFocusActive = isPlaylistPanelFocusActive(inQueueTrigger, inQueuePanel, pp, ex, ppRect);
  // 侧边歌单架 hover 焦点是否活跃。
  var shelfHoverFocus = !!(shelfCanFocus && isSideShelfFocusHit(e));
  if (queueFocusActive) {
    newFocus = 'queue';
  } else if (shelfManager && shelfManager.hasOpenContent && shelfManager.hasOpenContent()) {
    newFocus = 'shelf-detail';
  } else if (shelfHoverFocus) {
    newFocus = 'shelf-side';
  } else if (shelfCanFocus && shelfManager.getMode() === 'stage' && ey > H * 0.55) {
    newFocus = 'shelf-stage';
  }
  setFocusZone(newFocus, newFocus === 'queue');
});

// 推送壁纸状态到宿主；当前桥接实现为空。
function pushWallpaperState() {}
// 应用壁纸模式状态；当前只做开发锁归一化。
function applyWallpaperModeState() {
  normalizeDevelopmentLockedFxState();
}
// 同步桌面覆盖层状态；当前桥接实现为空。
function syncDesktopOverlayState() {}

// 全屏
// 请求宿主切换全屏。
function toggleFullscreen() {
  sendEchoHostCommand('window-control', { action: 'fullscreen' });
}

// ============================================================
//  启动
// ============================================================
// 绑定视觉控制台。
bindFxPanel();
// 应用保存的歌词色板。
applySavedLyricPaletteState();
// 绑定音量控件。
bindVolumeControls();
// 初始化控制条玻璃效果。
initControlGlassSurface();
// 绑定播放控制按钮动画。
bindPlayerControlAnimations();
scheduleUiWarmTask(function(){
  // 启动后延迟刷新玻璃位移贴图，并预编译当前 Three.js 场景。
  updateControlGlassDisplacementMap();
  try {
    if (renderer && renderer.compile && scene && camera) renderer.compile(scene, camera);
  } catch (e) {}
}, 900);
// 应用控制条自动隐藏偏好。
applyControlsAutoHidePreference();
// 应用壁纸模式初始状态。
applyWallpaperModeState(false);
// 初始化歌单架模式。
setShelfMode(fx.shelf);
// 初始化左侧队列常开状态。
applyPlaylistPanelPinState(false);
// 按保存配置创建可选视觉层。
if (fx.floatLayer) createFloatLayer();
if (fx.particleLyrics) createLyricsParticles();
if (fx.backCover) createBackCoverLayer();
// 初始化待机引导。
initIdleGuideCanvas();
// 启动时渲染播放队列。
safeRenderQueuePanel('startup');



// ===== js/11-main-loop-bridge.js =====

// ============================================================
//  主循环
// ============================================================
// 上一帧时间戳。
var prevTime = performance.now();
// 主循环性能计数器会挂到 window，便于宿主或调试面板观察实际帧率、跳帧和长帧数量。
// 渲染性能采样状态。
var renderPerfState = {
  // 当前渲染模式。
  mode: 'vsync',
  // 最近一次采样 FPS。
  fps: 0,
  // 当前采样窗口帧数。
  frames: 0,
  // 跳过的帧数。
  skipped: 0,
  // 长帧数量。
  longFrames: 0,
  // 上一次实际渲染时间。
  lastRenderAt: 0,
  // 上一次性能采样时间。
  lastSampleAt: performance.now()
};
// 暴露性能状态给调试和宿主。
window.__mineradioPerf = renderPerfState;
// 主循环是否已启动。
var mainLoopStarted = false;
// 主循环错误是否已上报。
var mainLoopErrorReported = false;
// 各视觉步骤错误上报标记。
var visualStepErrorReported = {};
function reportMainLoopError(error) {
  // 主循环异常只上报一次，避免同一错误每帧刷屏；桥接层仍继续工作，控制命令不受影响。
  if (mainLoopErrorReported) return;
  mainLoopErrorReported = true;
  console.warn('[EchoMusicBridge] 主循环异常，桥接层继续运行', error);
}
function safeVisualStep(label, fn) {
  // 可选视觉模块独立容错，某个模块失败时不会中断整帧渲染或播放器控制。
  try {
    fn();
  } catch (error) {
    if (visualStepErrorReported[label]) return;
    visualStepErrorReported[label] = true;
    console.warn('[EchoMusicBridge] 可选视觉步骤异常，已跳过本步骤: ' + label, error);
  }
}
function getAdaptiveRenderFps() {
  // 根据后台状态、可见模式和当前负载决定是否限帧；返回 0 表示跟随 requestAnimationFrame。
  if (isDeepBackgroundMode()) return 1;
  if (RENDER_VISIBLE_VSYNC) return 0;
  var tier = (typeof getRenderLoadTier === 'function') ? getRenderLoadTier() : 0;
  if (typeof isRenderInteractionActive === 'function' && isRenderInteractionActive()) {
    if (tier >= 2) return RENDER_INTERACTION_HUGE_FPS;
    if (tier >= 1) return RENDER_INTERACTION_LARGE_FPS;
    return RENDER_INTERACTION_FPS;
  }
  if (tier >= 2) return RENDER_HUGE_FPS;
  if (tier >= 1) return RENDER_LARGE_FPS;
  return RENDER_ACTIVE_FPS;
}
function shouldSkipAdaptiveRenderFrame(now) {
  // 限帧模式下直接跳过整帧视觉计算，减少隐藏窗口和重负载场景的 CPU/GPU 占用。
  var fps = getAdaptiveRenderFps();
  renderPerfState.mode = fps ? (fps + 'fps') : 'vsync';
  if (!fps) {
    renderPerfState.lastRenderAt = now;
    return false;
  }
  var minGap = 1000 / fps;
  if (now - renderPerfState.lastRenderAt < minGap) {
    renderPerfState.skipped += 1;
    return true;
  }
  renderPerfState.lastRenderAt = now;
  return false;
}
function sampleRenderPerf(now, dt) {
  // 每秒采样一次渲染性能，并顺带触发运行时缓存裁剪检查。
  renderPerfState.frames += 1;
  if (dt > 0.034) renderPerfState.longFrames += 1;
  if (now - renderPerfState.lastSampleAt >= 1000) {
    renderPerfState.fps = Math.round(renderPerfState.frames * 1000 / Math.max(1, now - renderPerfState.lastSampleAt));
    renderPerfState.frames = 0;
    renderPerfState.lastSampleAt = now;
  }
  maybeTrimRuntimeCaches(now);
}
function animate() {
  // 主循环只消费宿主已经推送的状态，不主动拉取网络或音频；每帧顺序是频谱分析、状态平滑、视觉更新、渲染。
  requestAnimationFrame(animate);
  try {
  // 当前帧时间戳。
  var now = performance.now();
  if (shouldSkipAdaptiveRenderFrame(now)) return;
  // 本帧时间步长，最长限制到 50ms。
  var dt = Math.min((now - prevTime) / 1000, 0.05);
  prevTime = now;
  sampleRenderPerf(now, dt);
  uniforms.uTime.value += dt;
  // 指针视差缓动。
  pointerParallax.x += (pointerTarget.x - pointerParallax.x) * 0.040;
  pointerParallax.y += (pointerTarget.y - pointerParallax.y) * 0.040;

  // 宿主频谱映射: 插件只消费 EchoMusic 推送的 bins/waveform/rms/peak。
  beatOnsetFlag = false;
  if (hasHostSpectrumFrame() && playing && audio && !audio.paused) {
    readHostFrequencyData(frequencyData);
    readHostWaveformData(timeDomainData);
    // 频谱长度。
    var len = frequencyData.length;
    // kick 低频区截止。
    var kickEnd  = 7;
    // 人声区截止。
    var vocalEnd = Math.min(len, 140);
    // 中频乐器区截止。
    var midEnd   = Math.min(len, 280);
    // 低频、中频、高频、人声和 RMS 累加值。
    var bKick = 0, mInst = 0, tHigh = 0, voc = 0, rms = 0;
    for (var i = 0; i < kickEnd; i++) bKick += frequencyData[i] / 255;
    for (var i = kickEnd; i < vocalEnd; i++) voc += frequencyData[i] / 255;
    for (var i = vocalEnd; i < midEnd; i++) mInst += frequencyData[i] / 255;
    for (var i = midEnd; i < len; i++) tHigh += frequencyData[i] / 255;
    for (var j = 0; j < timeDomainData.length; j++) {
      var tv = (timeDomainData[j] - 128) / 128;
      rms += tv * tv;
    }
    bKick /= kickEnd;
    voc /= (vocalEnd - kickEnd);
    mInst /= Math.max(1, midEnd - vocalEnd);
    tHigh /= Math.max(1, len - midEnd);
    rms = readHostSpectrumRms(Math.sqrt(rms / timeDomainData.length));

    // 动态峰值跟踪
    bassPeak = Math.max(bassPeak * 0.994, bKick, 0.030);
    midPeak  = Math.max(midPeak  * 0.993, mInst, 0.026);
    treblePeak = Math.max(treblePeak * 0.992, tHigh, 0.018);
    energyPeak = Math.max(energyPeak * 0.995, rms, 0.030);

    // 各频段相对峰值的归一化强度。
    var rb = Math.min(1, Math.pow(bKick / Math.max(0.038, bassPeak * 0.66), 0.78));
    var rm = Math.min(1, Math.pow(mInst / Math.max(0.025, midPeak  * 0.70), 0.86));
    var rt = Math.min(1, Math.pow(tHigh / Math.max(0.020, treblePeak * 0.74), 0.92));
    var re = Math.min(1, Math.pow(rms / Math.max(0.034, energyPeak * 0.68), 0.82));

    // 低频突增量。
    var bassOnset = Math.max(0, rb - smoothBass);
    // 总能量突增量。
    var energyOnset = Math.max(0, re - prevEnergy);
    prevEnergy = prevEnergy * 0.88 + re * 0.12;

    // 实时节拍引擎输出。
    var realtimeBeat = processRealtimeBeatEngine(dt);
    // 实时节拍优先用于镜头和粒子脉冲；预解析 beatmap 不可用时才承担主要触发职责。
    if (realtimeBeat && realtimeBeat.hit) {
      // 当前是否 DJ 模式。
      var dj = djMode.active;
      // DJ 节拍图是否覆盖当前播放时间。
      var djMapCoversCurrentTime = !dj || !currentDjBeatMap || !currentDjBeatMap.partialUntilSec || !audio || (audio.currentTime || 0) <= currentDjBeatMap.partialUntilSec - 1.25;
      // DJ 模式节拍图是否可用于相机。
      var djBeatMapReadyForCamera = dj && currentDjBeatMap && currentDjBeatMap.cameraBeats && currentDjBeatMap.cameraBeats.length >= 4 && djMapCoversCurrentTime;
      // 当前模式下节拍图是否可用于相机。
      var beatMapReadyForCamera = dj ? djBeatMapReadyForCamera : (currentBeatMap && currentBeatMap.cameraBeats && currentBeatMap.cameraBeats.length >= 4);
      // 是否还在等待离线节拍图。
      var waitingForBeatMap = false;
      // 实时 kick 触发帧判定。
      var liveKickFrame = dj
        ? (realtimeBeat.low > 0.48 && rb > 0.38 && bassOnset > 0.055 && energyOnset > 0.010 && (realtimeBeat.lowDominance || 0) > 0.82)
        : (realtimeBeat.low > 0.50 && rb > 0.42 && bassOnset > 0.070 && energyOnset > 0.016);
      // 强实时节拍判定。
      var liveStrongHit = dj
        ? (realtimeBeat.confidence > 0.60 && realtimeBeat.strength > 0.56 && realtimeBeat.score > 0.50 && liveKickFrame)
        : (realtimeBeat.confidence > 0.76 && realtimeBeat.strength > 0.70 && realtimeBeat.score > 0.56 && liveKickFrame);
      // 速度辅助节拍判定。
      var liveTempoHit = dj
        ? (realtimeBeat.tempoAssist && realtimeBeat.confidence > 0.62 && realtimeBeat.strength > 0.52 && realtimeBeat.low > 0.48 && (liveKickFrame || bassOnset > 0.046))
        : (realtimeBeat.tempoAssist && realtimeBeat.confidence > 0.80 && realtimeBeat.strength > 0.66 && realtimeBeat.low > 0.50 && bassOnset > 0.052);
      // 实时节拍是否允许作为离线节拍图补位。
      var liveFallbackOk = dj
        ? (liveStrongHit || liveTempoHit)
        : (waitingForBeatMap
          ? (liveStrongHit || liveTempoHit)
          : (realtimeBeat.confidence > 0.84 && realtimeBeat.strength > 0.80 && realtimeBeat.low > 0.54 && (liveKickFrame || realtimeBeat.score > 0.68)));
      if (!beatMapReadyForCamera && liveFallbackOk) {
        // 调度实时节拍相机事件。
        scheduleBeatCamera({
          time: realtimeBeat.time,
          strength: realtimeBeat.strength,
          confidence: realtimeBeat.confidence,
          low: realtimeBeat.low,
          body: realtimeBeat.body,
          snap: realtimeBeat.snap,
          mass: realtimeBeat.mass,
          sharpness: realtimeBeat.sharpness,
          combo: realtimeBeat.combo,
          impact: clamp01(realtimeBeat.strength * 0.46 + realtimeBeat.confidence * 0.20 + realtimeBeat.low * 0.28),
          preview: waitingForBeatMap,
          primary: true,
          dj: dj
        }, 'live');
      }
      if (!beatMapReadyForCamera && liveFallbackOk) {
        // 等待离线节拍图期间压低实时脉冲强度。
        var previewPulseScale = waitingForBeatMap && !dj ? 0.68 : 1;
        // 实时节拍粒子脉冲强度。
        var rtPulse = Math.min(dj ? 0.34 : (waitingForBeatMap ? 0.46 : 0.62), realtimeBeat.strength * (realtimeBeat.tempoAssist ? (dj ? 0.42 : 0.62) : (dj ? 0.48 : 0.68)) * previewPulseScale);
        if (rtPulse > beatPulse + 0.09) beatOnsetFlag = true;
        beatPulse = Math.max(beatPulse, rtPulse);
      }
    } else if (bassOnset > 0.075 && rb > 0.32 && energyOnset > 0.020) {
      beatPulse = Math.max(beatPulse, Math.min(0.12, bassOnset * 0.18));
    }
    beatPulse *= Math.pow(0.36, dt);

    // v7.2+: 预解析 beatmap 只在实时引擎暂时没锁住时补位.
    tickDjBeatMap();
    tickBeatMap();
    if (scheduledBeatFlag) {
      beatOnsetFlag = true;
      scheduledBeatFlag = false;
    }
    // scheduledBeatPulse 衰减并合并到 beatPulse
    if (scheduledBeatPulse > beatPulse) beatPulse = scheduledBeatPulse;
    scheduledBeatPulse *= Math.pow(0.32, dt);

    // 简单包络跟随函数。
    function env(prev, next, attack, release) {
      // 上升和下降使用不同响应速度。
      var k = next > prev ? attack : release;
      return prev + (next - prev) * k;
    }
    // smoothBass 主要由 kick 驱动 (不被人声干扰)
    smoothBass  = env(smoothBass, Math.min(0.82, rb * 0.78 + re * 0.025), 0.28, 0.075);
    // smoothMid 用 中高乐器, 不再混入人声
    smoothMid   = env(smoothMid,  Math.min(0.68, rm * 0.64 + re * 0.025), 0.18, 0.060);
    smoothTreb  = env(smoothTreb, Math.min(0.56, rt * 0.54), 0.18, 0.055);
    smoothEnergy= env(smoothEnergy, Math.min(0.72, re), 0.16, 0.055);
    updateCinemaDynamics(re, rb);
    updateCinemaTrackProfile({ energy: re, low: rb, vocal: voc, melody: rm, lowOnset: bassOnset, energyOnset: energyOnset });
    // 歌词阳光溢光: 独立于律动强度, 看持续能量 + 中高频抬升, 更像副歌/高音段落而不是单个鼓点.
    // 持续能量分量。
    var sunEnergy = clamp01((smoothEnergy - 0.18) / 0.38);
    // 人声分量。
    var sunVoice = clamp01((voc - 0.11) / 0.34);
    // 旋律中频分量。
    var sunMelody = clamp01((smoothMid - 0.16) / 0.27);
    // 空气高频分量。
    var sunAir = clamp01((smoothTreb - 0.105) / 0.17);
    // 合成阳光溢光原始强度。
    var sunRaw = clamp01(sunEnergy * 0.36 + sunVoice * 0.18 + sunMelody * 0.26 + sunAir * 0.20);
    sunRaw = sunRaw * sunRaw * (3 - 2 * sunRaw);
    lyricSunAvg += (sunRaw - lyricSunAvg) * 0.006;
    lyricSunPeak = Math.max(0.48, lyricSunPeak * 0.9985, sunRaw);
    // 动态阈值，避免安静段误触发太阳光。
    var sunThreshold = Math.max(0.78, lyricSunAvg + 0.20, lyricSunPeak * 0.74);
    // 超过阈值后的门控强度。
    var sunGate = clamp01((sunRaw - sunThreshold) / Math.max(0.08, 1.0 - sunThreshold));
    sunGate = sunGate * sunGate * (3 - 2 * sunGate);
    lyricSunHold += (sunGate - lyricSunHold) * (sunGate > lyricSunHold ? 0.035 : 0.014);
    lyricSunTarget = lyricSunHold > 0.16 ? clamp01((lyricSunHold - 0.16) / 0.84) : 0;
    lyricSunEnergy += (lyricSunTarget - lyricSunEnergy) * (lyricSunTarget > lyricSunEnergy ? 0.075 : 0.030);
  } else {
    // 无频谱或未播放时，各能量状态自然衰减。
    smoothBass *= 0.91; smoothMid *= 0.91; smoothTreb *= 0.91; smoothEnergy *= 0.91; beatPulse *= 0.82;
    liveCamAvg *= 0.94;
    liveCamPeak = Math.max(0.28, liveCamPeak * 0.98);
    liveCamLastRaw *= 0.80;
    lyricSunTarget = 0;
    lyricSunHold *= 0.90;
    lyricSunEnergy *= 0.92;
    lyricSunAvg *= 0.995;
    lyricSunPeak = Math.max(0.48, lyricSunPeak * 0.997);
  }
  // 全局音频能量。
  audioEnergy = Math.max(smoothEnergy, beatPulse * 0.30);
  // 最终低频视觉强度。
  bass = Math.min(0.90, smoothBass * 1.05 + beatPulse * 0.18) * fx.intensity;
  // 最终中频视觉强度。
  mid  = Math.min(0.72, smoothMid * 1.12) * fx.intensity;
  // 最终高频视觉强度。
  treble = Math.min(0.62, smoothTreb * 1.20) * fx.intensity;
  if (fx.preset >= 4) {
    // 壁纸预设使用更克制的音频响应。
    var wallpaperAudio = fx.preset === 5;
    // 圆环低频响应。
    var ringBass = smoothBass * (wallpaperAudio ? 1.10 : 1.58) + beatPulse * (wallpaperAudio ? 0.18 : 0.42) - smoothMid * 0.16 - smoothTreb * 0.06;
    // 圆环中频响应。
    var ringMid = smoothMid * (wallpaperAudio ? 1.16 : 1.82) - smoothBass * 0.14 - smoothTreb * 0.07;
    // 圆环高频响应。
    var ringTreble = smoothTreb * (wallpaperAudio ? 1.34 : 2.28) - smoothMid * 0.10 - smoothBass * 0.05;
    bass = Math.pow(clamp01((ringBass - 0.050) / 0.58), 0.72) * fx.intensity;
    mid = Math.pow(clamp01((ringMid - 0.045) / 0.46), 0.78) * fx.intensity;
    treble = Math.pow(clamp01((ringTreble - 0.030) / 0.34), 0.84) * fx.intensity;
    if (wallpaperAudio) {
      bass = Math.min(bass, 0.46 * fx.intensity);
      mid = Math.min(mid, 0.40 * fx.intensity);
      treble = Math.min(treble, 0.36 * fx.intensity);
      beatPulse *= 0.34;
    }
  }
  if (djMode.active) {
    // DJ 模式下提升低频脉冲和段落能量。
    bass = Math.min(1.00, bass * 1.06 + beatPulse * 0.085);
    mid = Math.min(0.76, mid * 1.00 + clamp01(djMode.sectionChange * 1.6) * 0.020);
    treble = Math.min(0.66, treble * 0.98);
    audioEnergy = Math.max(audioEnergy, beatPulse * 0.38, djMode.sectionEnergy * 0.54);
  }

  // 唱片旋转速度倍率。
  var vinylSpeedMul = isFinite(fx.speed) ? Math.max(0.05, fx.speed) : 1;
  // 唱片本帧旋转速度。
  var vinylSpinSpeed = (0.40 + smoothBass * 0.09) * vinylSpeedMul;
  uniforms.uVinylSpin.value = (uniforms.uVinylSpin.value + dt * vinylSpinSpeed) % (Math.PI * 2);

  updateParticlePointerFrame();
  // 写入 shader 音频强度 uniform。
  uniforms.uBass.value   = bass;
  uniforms.uMid.value    = mid;
  uniforms.uTreble.value = treble;
  uniforms.uBeat.value   = beatPulse;
  uniforms.uEnergy.value = audioEnergy;
  uniforms.uMouseXY.value.set(mouseWorld.x, mouseWorld.y);
  uniforms.uMouseActive.value = mouseActive ? 1 : 0;
  // 骷髅预设默认背景压暗值。
  var skullBackdropDim = fx && fx.preset === SKULL_PRESET_INDEX ? 0.58 : 1;
  // 歌单架或骷髅预设要求的粒子压暗目标。
  var shelfDimTarget = shouldDimWallpaperForShelf() ? 0.48 : skullBackdropDim;
  // 粒子压暗缓动速度。
  var shelfDimEase = shelfDimTarget < uniforms.uParticleDim.value ? 0.18 : 0.10;
  uniforms.uParticleDim.value += (shelfDimTarget - uniforms.uParticleDim.value) * Math.min(1, shelfDimEase * Math.max(1, dt * 60));

  // 通用转场脉冲: 只作为切换预设时的短促提亮。
  uniforms.uBurstAmt.value *= 0.90;
  tickPresetTransition();

  updateRipples(dt);
  updateFloatLayer(dt);
  // 共享主循环里只允许单个可选视觉模块失败，不让错误扩散到 renderer.render。
  if (shelfManager) safeVisualStep('playlist-shelf', function(){ shelfManager.update(dt); });
  tickLyricsParticles();

  // 电影镜头
  updateCinema(dt);
  updateFreeCamera(dt);
  updateCamera();
  applySkullCameraPose(dt);

  // v7.2 旋转 = 头部+眼球追踪 + 鼠标拖动 + 惯性
  tickParticleSpin(dt);
  // 骷髅预设是否激活。
  var skullPresetActive = fx && fx.preset === SKULL_PRESET_INDEX;
  // 骷髅预设接管主粒子层时隐藏普通封面粒子。
  particles.visible = !skullPresetActive;
  if (bloomParticles) bloomParticles.visible = !skullPresetActive && fx.bloom && fx.bloomStrength > 0.01;
  if (floatGroup) floatGroup.visible = !skullPresetActive;
  if (backCoverGroup) backCoverGroup.visible = !skullPresetActive;
  // 粒子目标 Y 旋转。
  var targetRotY = orbit.centerLocked ? 0 : (headParallax.active ? headParallax.x * 0.5 : 0) + particleRotation.y;
  // 粒子目标 X 旋转。
  var targetRotX = orbit.centerLocked ? 0 : (headParallax.active ? -headParallax.y * 0.35 : 0) + particleRotation.x;
  particles.rotation.y += (targetRotY - particles.rotation.y) * 0.055;
  particles.rotation.x += (targetRotX - particles.rotation.x) * 0.055;
  if (bloomParticles) {
    bloomParticles.rotation.copy(particles.rotation);
  }
  // 同步给背面粒子层
  if (floatGroup) {
    floatGroup.rotation.copy(particles.rotation);
  }
  if (backCoverGroup) {
    backCoverGroup.rotation.copy(particles.rotation);
  }
  updateSkullParticleLayer(dt);
  updateStageLyrics3D(dt);
  syncDesktopOverlayState();

  // 缩略图脉动
  if (currentIdx >= 0) {
    // 缩略封面随低频轻微缩放。
    var s = 1 + bass * 0.08;
    // 缩略封面节点。
    var thumbCoverEl = document.getElementById('thumb-cover');
    if (thumbCoverEl) thumbCoverEl.style.transform = 'scale(' + s + ')';
  }

// 渲染当前场景。
renderer.render(scene, camera);
  } catch (error) {
    reportMainLoopError(error);
  }
}
// 安全启动主循环。
function startMainLoopSafely() {
  // 统一启动入口防止重复 requestAnimationFrame；失败时仍保留桥接层的消息处理能力。
  if (mainLoopStarted) return;
  mainLoopStarted = true;
  try {
    requestAnimationFrame(animate);
  } catch (error) {
    reportMainLoopError(error);
  }
}

// ============================================================
//  EchoMusic 插件桥接层
// ============================================================
(function initEchoMusicPluginBridge() {
  // 桥接层运行在 iframe 子页面内：接收父页面推送的快照、歌词、进度和频谱，并把用户操作回传给宿主。
  // 原播放器的大部分 UI 和视觉逻辑继续复用，但真实播放、队列修改和窗口控制都交给 EchoMusic 宿主执行。
  // 宿主消息 source 标识。
  var BRIDGE_PARENT_SOURCE = 'echo-player-frontend-parent';
  // 子页面消息 source 标识。
  var BRIDGE_CHILD_SOURCE = 'echo-player-frontend-child';
  // 最近一次宿主快照。
  var bridgeSnapshot = null;
  // 桥接频谱帧引用。
  var bridgeSpectrum = hostSpectrumFrame;
  // 最近一次封面地址。
  var bridgeLastCover = '';
  // 最近一次队列签名。
  var bridgeQueueKey = '';
  // 最近一次歌词签名。
  var bridgeLyricKey = '';
  // 宿主播放时钟锚点。
  var bridgePlaybackClock = { time: 0, duration: 0, playing: false, rate: 1, receivedAt: 0 };
  // 宿主控制能力。
  var bridgeHostControls = { platform: '', showFullscreenButton: true, canShowMiniPlayer: false };
  // 播放/暂停乐观状态。
  var bridgePlaybackPending = null;
  // 歌词是否被桥接层强制打开过。
  var bridgeLyricsForcedOpen = false;
  // 播放/暂停乐观状态超时时间。
  var BRIDGE_PLAYBACK_PENDING_TIMEOUT = 1800;

  // 向父页面发送桥接协议消息。
  function post(type, extra) {
    // 子页面发给宿主的消息统一带 source，父页面只接受这个来源，避免误处理其他窗口消息。
    try {
      parent.postMessage(Object.assign({
        source: BRIDGE_CHILD_SOURCE,
        type: type
      }, extra || {}), '*');
    } catch (e) {}
  }

  // 发送宿主播放器控制命令。
  function command(name, payload) {
    // 所有控制命令都收敛成统一协议，宿主侧再映射到真实播放器 API。
    post('echo-player-frontend:command', Object.assign({ command: name }, payload || {}));
  }
  // 暴露调试命令入口，便于宿主或控制台直接发送桥接命令。
  window.__echoBridgeCommand = command;

  // 获取桥接层使用的高精度时间。
  function bridgeNow() {
    return typeof performance !== 'undefined' && typeof performance.now === 'function'
      ? performance.now()
      : Date.now();
  }

  // 判断播放/暂停乐观状态是否仍在有效期内。
  function isBridgePlaybackPendingActive() {
    // 播放/暂停采用本地乐观状态，等待宿主确认；超过超时时间仍未确认则回到宿主实际状态。
    if (!bridgePlaybackPending) return false;
    if (bridgeNow() - bridgePlaybackPending.startedAt > BRIDGE_PLAYBACK_PENDING_TIMEOUT) {
      bridgePlaybackPending = null;
      return false;
    }
    return true;
  }

  // 合并宿主播放状态与本地乐观播放状态。
  function resolveBridgePlaybackPlaying(hostPlaying) {
    // 宿主播放状态布尔化。
    var normalized = !!hostPlaying;
    if (!isBridgePlaybackPendingActive()) return normalized;
    if (bridgePlaybackPending.targetPlaying === normalized) {
      bridgePlaybackPending = null;
      return normalized;
    }
    return bridgePlaybackPending.targetPlaying;
  }

  // 立即应用本地播放状态到 UI 和伪 audio。
  function applyLocalPlaybackState(nextPlaying) {
    // 先更新本地 UI 和伪 audio 状态，让按钮、进度条和歌词立即响应用户点击。
    // 目标播放状态。
    nextPlaying = !!nextPlaying;
    bridgePlaybackClock.time = bridgeCurrentTime();
    bridgePlaybackClock.playing = nextPlaying;
    bridgePlaybackClock.receivedAt = bridgeNow();
    playing = nextPlaying;
    if (audio) {
      audio.paused = !nextPlaying;
      audio.ended = false;
    }
    if (bridgeSnapshot) {
      bridgeSnapshot.currentTime = bridgePlaybackClock.time;
      bridgeSnapshot.isPlaying = nextPlaying;
    }
    if (typeof setPlayIcon === 'function') setPlayIcon(nextPlaying);
    if (typeof updatePlaybackProgressUi === 'function') updatePlaybackProgressUi();
  }

  // 请求宿主切换播放状态。
  function requestBridgePlayback(nextPlaying) {
    // 播放请求先记录目标状态，再发送宿主命令；后续 progress/snapshot 会清掉 pending。
    nextPlaying = !!nextPlaying;
    bridgePlaybackPending = {
      targetPlaying: nextPlaying,
      startedAt: bridgeNow()
    };
    applyLocalPlaybackState(nextPlaying);
    command(nextPlaying ? 'play' : 'pause');
  }

  // 切换当前播放状态。
  function toggleBridgePlayback() {
    // 当前有效播放状态，pending 状态优先。
    var currentPlaying = isBridgePlaybackPendingActive()
      ? bridgePlaybackPending.targetPlaying
      : !!playing;
    requestBridgePlayback(!currentPlaying);
  }

  // 把数字夹到 0..1。
  function clamp01(value) {
    value = Number(value) || 0;
    return Math.max(0, Math.min(1, value));
  }

  // 设置桥接播放时钟当前时间。
  function setBridgeClockTime(value) {
    bridgePlaybackClock.time = Math.max(0, Number(value) || 0);
    bridgePlaybackClock.receivedAt = bridgeNow();
  }

  // 根据宿主锚点和本地时间差计算当前播放时间。
  function bridgeCurrentTime() {
    // 子页面用宿主最近一次进度作为锚点，本地按时间差外推，避免 100ms 推送间隔造成进度卡顿。
    var t = Math.max(0, Number(bridgePlaybackClock.time) || 0);
    if (bridgePlaybackClock.playing) {
      t += Math.max(0, performance.now() - (bridgePlaybackClock.receivedAt || performance.now())) * 0.001 * Math.max(0.25, Math.min(4, Number(bridgePlaybackClock.rate) || 1));
    }
    if (bridgePlaybackClock.duration > 0) t = Math.min(bridgePlaybackClock.duration + 0.12, t);
    return Math.max(0, t);
  }

  // 应用宿主推送的定位包（事件驱动，取代高频进度轮询）。
  function applyPositionPayload(payload) {
    payload = payload || {};
    var positionMs = Number(payload.position_ms);
    var durationMs = Number(payload.duration_ms);
    if (!isFinite(positionMs)) positionMs = Number(payload.currentTime || 0) * 1000;
    if (!isFinite(durationMs)) durationMs = Number(payload.duration || 0) * 1000;
    var hostPlaying = payload.is_playing != null ? !!payload.is_playing : !!payload.isPlaying;
    // 合并本地乐观状态后的播放状态。
    var effectivePlaying = resolveBridgePlaybackPlaying(hostPlaying);
    bridgePlaybackClock.time = Math.max(0, positionMs || 0) / 1000;
    bridgePlaybackClock.duration = Math.max(0, durationMs || 0) / 1000;
    bridgePlaybackClock.playing = effectivePlaying;
    bridgePlaybackClock.receivedAt = bridgeNow();
    playing = bridgePlaybackClock.playing;
    if (audio) {
      audio.paused = !playing;
      audio.ended = false;
      audio.duration = bridgePlaybackClock.duration;
    }
    if (bridgeSnapshot) {
      bridgeSnapshot.currentTime = bridgePlaybackClock.time;
      bridgeSnapshot.duration = bridgePlaybackClock.duration;
      bridgeSnapshot.isPlaying = playing;
    }
    if (typeof setPlayIcon === 'function') setPlayIcon(playing);
    if (typeof updatePlaybackProgressUi === 'function') updatePlaybackProgressUi();
  }

  // 转义 CSS url 中的双引号。
  function escapeCssUrl(value) {
    return String(value || '').replace(/"/g, '\\"');
  }

  // 将宿主播放模式映射到旧播放器内部模式。
  function hostModeToMine(mode) {
    mode = String(mode || '');
    if (mode === 'random') return 'shuffle';
    if (mode === 'single') return 'single';
    return 'loop';
  }

  // 从宿主歌曲对象提取封面地址。
  function bridgeSongCover(song) {
    song = song || {};
    return String(song.cover || song.coverUrl || song.picUrl || song.albumCover || song.albumImg || song.img || song.image || song.cover_url || '');
  }

  // 归一化宿主歌曲对象为旧播放器内部歌曲模型。
  function normalizeBridgeSong(song) {
    // 宿主歌曲结构在不同来源下字段不完全一致，桥接层统一成旧播放器内部使用的歌曲模型。
    song = song || {};
    // 归一化后的封面地址。
    var cover = bridgeSongCover(song);
    return {
      // 旧播放器列表和 DOM key 使用的主 id。
      id: String(song.id || song.hash || ''),
      // 兼容旧播放队列逻辑中的 hash 字段。
      hash: String(song.hash || song.id || ''),
      // 主标题，缺省时给出稳定占位。
      name: String(song.name || song.title || '未知歌曲'),
      // 兼容部分 UI 仍读取 title 的路径。
      title: String(song.title || song.name || '未知歌曲'),
      // 歌手名，缺省时给出稳定占位。
      artist: String(song.artist || '未知歌手'),
      // 旧封面字段。
      cover: cover,
      // 新旧代码兼容的封面字段。
      coverUrl: cover,
      // 专辑名。
      album: String(song.album || ''),
      // 歌曲时长，单位沿用宿主传入值。
      duration: Number(song.duration || 0),
      // 标记歌曲来自 EchoMusic 宿主。
      source: 'echo'
    };
  }

  // 注入桥接层专用样式。
  function installBridgeStyle() {
    // iframe 内补充宿主窗口控制按钮样式，避免依赖外层应用的全局样式。
    if (document.getElementById('echo-plugin-bridge-style')) return;
    // 运行时样式节点。
    var style = document.createElement('style');
    style.id = 'echo-plugin-bridge-style';
    // close 按钮和窗口控制按钮的最小样式集合。
    style.textContent = [
      '#echo-bridge-close{position:fixed;z-index:80;top:8px;left:16px;right:auto;width:32px;height:32px;display:flex;align-items:center;justify-content:center;border:0;border-radius:50%;background:transparent;color:rgba(255,255,255,.7);cursor:pointer;padding:0;transition:color .2s ease,background .2s ease}',
      '#echo-bridge-close:hover{color:#fff;background:rgba(255,255,255,.1)}',
      '#echo-bridge-close svg{width:20px;height:20px;display:block;stroke:currentColor}',
      '#echo-bridge-window-controls{position:fixed;z-index:80;top:0;right:0;height:48px;display:flex;align-items:center;color:rgba(255,255,255,.72)}',
      '.echo-bridge-window-control{width:48px;height:48px;display:flex;align-items:center;justify-content:center;border:0;background:transparent;color:inherit;cursor:pointer;padding:0;transition:color .2s ease,background .2s ease,opacity .2s ease}',
      '.echo-bridge-window-control:hover{color:#fff;background:rgba(255,255,255,.1)}',
      '.echo-bridge-window-control--mini{width:40px}',
      '.echo-bridge-window-control--mini:hover{background:transparent;color:var(--color-primary,#31cfa1)}',
      '.echo-bridge-window-control--close:hover{background:#ff3b30;color:#fff}',
      '.echo-bridge-window-control svg{width:14px;height:14px;display:block;stroke:currentColor;fill:none}',
      '.echo-bridge-window-control--mini svg{width:16px;height:16px}'
    ].join('\n');
    document.head.appendChild(style);
  }

  // 安装左上角返回按钮。
  function installCloseButton() {
    if (document.getElementById('echo-bridge-close')) return;
    // 返回按钮节点。
    var button = document.createElement('button');
    button.id = 'echo-bridge-close';
    button.type = 'button';
    button.title = '返回';
    button.setAttribute('aria-label', '返回');
    button.innerHTML = '<svg viewBox="0 0 24 24" fill="none" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="m6 9 6 6 6-6"></path></svg>';
    button.addEventListener('click', function(e) {
      // 返回按钮只通知宿主关闭或收起当前 iframe 页面。
      e.preventDefault();
      command('close');
    });
    document.body.appendChild(button);
  }

  // 返回桥接窗口按钮使用的内联 SVG 图标。
  function bridgeIcon(name) {
    // mini 模式图标。
    if (name === 'mini') return '<svg viewBox="0 0 24 24" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><rect x="3" y="5" width="18" height="14" rx="2"></rect><path d="M8 13h6v4H8z"></path></svg>';
    // 最小化图标。
    if (name === 'minimize') return '<svg viewBox="0 0 24 24" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M5 12h14"></path></svg>';
    // 全屏图标。
    if (name === 'fullscreen') return '<svg viewBox="0 0 24 24" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M3 7V3h4"></path><path d="M21 7V3h-4"></path><path d="M3 17v4h4"></path><path d="M21 17v4h-4"></path></svg>';
    // 最大化图标。
    if (name === 'maximize') return '<svg viewBox="0 0 24 24" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><rect x="6" y="6" width="12" height="12" rx="1.5"></rect></svg>';
    // 默认返回关闭图标。
    return '<svg viewBox="0 0 24 24" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M18 6 6 18"></path><path d="m6 6 12 12"></path></svg>';
  }

  // 根据按钮配置创建一个宿主窗口控制按钮。
  function createBridgeWindowButton(options) {
    // 窗口控制按钮节点。
    var button = document.createElement('button');
    button.type = 'button';
    button.className = 'echo-bridge-window-control' + (options.extraClass ? ' ' + options.extraClass : '');
    button.title = options.title;
    button.setAttribute('aria-label', options.title);
    button.innerHTML = bridgeIcon(options.icon);
    button.addEventListener('click', function(e) {
      // 窗口按钮事件只发送给宿主，由宿主操作真实窗口。
      e.preventDefault();
      if (options.command === 'mini-player') {
        command('mini-player');
      } else {
        command('window-control', { action: options.action });
      }
    });
    return button;
  }

  // 根据宿主能力安装窗口控制按钮组。
  function installWindowControls() {
    // 旧按钮组需要先移除，避免宿主能力变更后残留按钮。
    var existing = document.getElementById('echo-bridge-window-controls');
    if (existing) existing.remove();

    // macOS 使用宿主原生红绿灯按钮，子页面不再绘制右侧窗口按钮。
    var isMac = String(bridgeHostControls.platform || '').toLowerCase() === 'darwin';
    // 将要渲染的按钮配置列表。
    var buttons = [];
    if (bridgeHostControls.canShowMiniPlayer) {
      buttons.push({ title: 'mini 模式', icon: 'mini', command: 'mini-player', extraClass: 'echo-bridge-window-control--mini' });
    }
    if (!isMac) {
      buttons.push({ title: '最小化', icon: 'minimize', action: 'minimize' });
      if (bridgeHostControls.showFullscreenButton !== false) {
        buttons.push({ title: '全屏', icon: 'fullscreen', action: 'fullscreen' });
      }
      buttons.push({ title: '最大化', icon: 'maximize', action: 'maximize' });
      buttons.push({ title: '关闭', icon: 'close', action: 'close', extraClass: 'echo-bridge-window-control--close' });
    }
    if (!buttons.length) return;

    // 右上角窗口控制容器。
    var controls = document.createElement('div');
    controls.id = 'echo-bridge-window-controls';
    buttons.forEach(function(options) {
      // 逐个创建并插入窗口控制按钮。
      controls.appendChild(createBridgeWindowButton(options));
    });
    document.body.appendChild(controls);
  }

  // 安装宿主播放代理 audio 对象。
  function installAudioShim() {
    // 旧播放器内部大量逻辑依赖 audio 对象；这里用伪 audio 接管读写，并把播放控制转成宿主命令。
    // 伪 audio 只维护状态和访问器，不创建真实媒体流。
    audio = {
      // 当前暂停状态。
      paused: true,
      // 桥接模式不使用 HTMLMediaElement ended 事件。
      ended: false,
      // 当前时间通过宿主时钟外推。
      get currentTime() { return bridgeCurrentTime(); },
      // seek 写入本地时钟，具体跳转由命令触发。
      set currentTime(value) { setBridgeClockTime(value); },
      // 当前总时长。
      duration: 0,
      // 播放速度。
      playbackRate: 1,
      // 占位 src，避免旧代码把 audio 当成未初始化。
      src: 'echo-plugin-host',
      // 兼容旧封面/音频逻辑读取跨域字段。
      crossOrigin: 'anonymous',
      // 事件接口占位，兼容旧绑定代码。
      addEventListener: function() {},
      // 事件解绑接口占位。
      removeEventListener: function() {},
      // load 接口占位。
      load: function() {},
      // play 被旧代码调用时转成宿主播放命令。
      play: function() { requestBridgePlayback(true); return Promise.resolve(); },
      // pause 被旧代码调用时转成宿主暂停命令。
      pause: function() { requestBridgePlayback(false); },
    };
  }

  // 强制旧播放器界面进入桥接模式首屏。
  function forcePlayerSurface() {
    // 标记桥接模式，显示底部控制条，确保 iframe 首屏就是可交互播放器。
    document.body.classList.add('echo-plugin-bridge');
    var bottom = document.getElementById('bottom-bar');
    if (bottom) bottom.classList.add('visible');
    setControlsHidden(false);
    forcePlaybackControlsInteractive();
  }

  // 请求刷新 Three.js 主渲染视口。
  function refreshBridgeViewport(reason) {
    try {
      if (typeof scheduleMainRendererViewportRefresh === 'function') {
        scheduleMainRendererViewportRefresh(reason || 'echo-bridge');
      }
    } catch (error) {
      console.warn('[EchoMusicBridge] 视口刷新失败', error);
    }
  }

  // 请求从后台恢复视觉层。
  function recoverBridgeVisuals(reason) {
    try {
      if (typeof recoverVisualsAfterBackground === 'function') {
        recoverVisualsAfterBackground(reason || 'echo-bridge');
      }
    } catch (error) {
      console.warn('[EchoMusicBridge] 视觉恢复失败', error);
    }
  }

  // 唤醒桥接模式下的视觉渲染表面。
  function revealBridgeVisualSurface() {
    // 收到有效宿主快照后唤醒视觉层，处理后台恢复、加载态清理和粒子透明度渐入。
    refreshBridgeViewport('echo-bridge-snapshot');
    recoverBridgeVisuals('echo-bridge-snapshot');
    if (typeof markRenderInteraction === 'function') markRenderInteraction('echo-bridge-snapshot', 1200);
    if (typeof uniforms === 'undefined' || !uniforms) return;
    if (uniforms.uLoading) {
      try {
        if (typeof forceLoadingSettled === 'function') forceLoadingSettled('echo-bridge-snapshot');
        else uniforms.uLoading.value = 0;
      } catch (error) {
        console.warn('[EchoMusicBridge] 加载态清理失败', error);
        uniforms.uLoading.value = 0;
      }
    }
    if (!uniforms.uAlpha) return;

    // 当前主粒子透明度。
    var currentAlpha = Number(uniforms.uAlpha.value || 0);
    if (currentAlpha >= 0.98) return;
    if (typeof firstPlayDone !== 'undefined') firstPlayDone = true;

    try {
      // 优先走用户预设粒子显隐函数，缺失时退回通用透明度补间。
      if (typeof revealUserPresetParticles === 'function') {
        revealUserPresetParticles({ alpha: 1.0, duration: 260 });
      } else if (typeof tweenParticleAlpha === 'function') {
        tweenParticleAlpha(currentAlpha, 1.0, 260);
      } else {
        uniforms.uAlpha.value = 1.0;
      }
    } catch (error) {
      console.warn('[EchoMusicBridge] 视觉层唤醒失败', error);
      uniforms.uAlpha.value = 1.0;
    }
  }

  // 确保桥接模式默认开启粒子歌词。
  function ensureBridgeLyricsEnabled() {
    // 桥接模式默认打开粒子歌词，确保从宿主歌词页进入时能立刻看到歌词舞台。
    if (bridgeLyricsForcedOpen) return;
    bridgeLyricsForcedOpen = true;
    if (typeof setParticleLyricsSilently === 'function') {
      try {
        setParticleLyricsSilently(true);
      } catch (error) {
        console.warn('[EchoMusicBridge] 歌词首屏开启失败', error);
        if (typeof fx === 'object' && fx) fx.particleLyrics = true;
        lyricsVisible = true;
      }
    } else if (typeof fx === 'object' && fx) {
      fx.particleLyrics = true;
      lyricsVisible = true;
    }
  }

  // 刷新歌词渲染表面。
  function refreshBridgeLyricsSurface() {
    if (fx && fx.particleLyrics && typeof createLyricsParticles === 'function') {
      try {
        createLyricsParticles();
      } catch (error) {
        console.warn('[EchoMusicBridge] 歌词粒子刷新失败', error);
      }
      return;
    }
    if (typeof renderLyrics === 'function') renderLyrics();
  }

  // 设置桥接等待宿主歌曲的空态。
  function setBridgeWaitingState(waiting) {
    // 是否进入等待态。
    waiting = !!waiting;
    document.body.classList.toggle('bridge-waiting', waiting);
    if (!waiting) return;
    // 控制条曲名节点。
    var controlTitle = document.getElementById('control-title');
    // 控制条歌手节点。
    var controlArtist = document.getElementById('control-artist');
    // 控制条封面节点。
    var controlCover = document.getElementById('control-cover');
    // 播放时间显示节点。
    var timeDisplay = document.getElementById('time-display');
    if (controlTitle) controlTitle.textContent = '等待 EchoMusic';
    if (controlArtist) controlArtist.textContent = '播放歌曲后将在这里显示歌词';
    if (controlCover) controlCover.classList.add('cover-empty');
    if (timeDisplay) timeDisplay.textContent = '0:00 / 0:00';
    if (typeof setPlayIcon === 'function') setPlayIcon(false);
    if (typeof setProgressVisual === 'function') setProgressVisual(0);
  }

  // 应用宿主当前歌曲封面到 UI 和粒子纹理链路。
  function applyCover(song) {
    // 当前歌曲封面地址。
    var cover = bridgeSongCover(song);
    if (cover === bridgeLastCover) return;
    bridgeLastCover = cover;
    // 右下角缩略封面图片。
    var thumb = document.getElementById('thumb-cover');
    if (thumb) {
      if (cover) thumb.src = cover;
      else thumb.removeAttribute('src');
    }
    if (typeof setControlCoverSrc === 'function') setControlCoverSrc(cover);
    // 背景专辑图节点。
    var albumBg = document.getElementById('album-bg');
    if (albumBg) {
      if (cover) {
        albumBg.style.backgroundImage = 'url("' + escapeCssUrl(cover) + '")';
        albumBg.classList.add('visible');
      } else {
        albumBg.style.backgroundImage = '';
        albumBg.classList.remove('visible');
      }
    }
    if (cover && typeof applyCoverDataUrl === 'function' && isInlineCoverSrc(cover)) {
      // 内联封面直接走 data url 解码链路。
      try { applyCoverDataUrl(cover, { deferHeavy: true, timeout: 1600 }); } catch (e) {}
    } else if (cover && typeof loadCoverFromUrl === 'function' && /^https?:\/\//i.test(cover)) {
      // 远程封面走 URL 加载链路。
      try { loadCoverFromUrl(cover, { deferHeavy: true, timeout: 1600 }); } catch (e) {}
    } else if (!cover && typeof loadCoverFromUrl === 'function') {
      // 无封面时触发旧链路清理封面纹理。
      try { loadCoverFromUrl('', { deferHeavy: true, timeout: 1600 }); } catch (e) {}
    }
  }

  // 应用宿主推送的歌词载荷。
  function applyLyricsPayload(payload) {
    // 歌词包用 key 去重；逐字歌词会保留到 characters，没有逐字时退回行级时间。
    payload = payload || {};
    // 宿主歌词行数组。
    var lines = Array.isArray(payload.lines) ? payload.lines : [];
    // 歌词去重签名，优先使用宿主 key，否则按行时间、文本和逐字时间生成。
    var key = payload.key || (lines.length + '|' + lines.map(function(line) {
      // 当前行逐字歌词数组。
      var chars = Array.isArray(line.characters) ? line.characters : [];
      // 当前行逐字歌词签名。
      var charKey = chars.map(function(character) {
        // 单字文本和起止时间组成稳定签名。
        return [character && (character.text != null ? character.text : character.t) || '', character && (character.startTime != null ? character.startTime : character.s) || 0, character && (character.endTime != null ? character.endTime : character.e) || 0].join(',');
      }).join(';');
      // 行级时间、主文本、翻译文本和逐字签名组成整行签名。
      return [line.time_ms || line.t || line.time || 0, line.text || '', line.secondary || '', charKey].join(':');
    }).join('|'));
    if (key === bridgeLyricKey) return;
    bridgeLyricKey = key;
    lyricsLines = lines.map(function(line, index) {
      // 当前行开始时间，宿主优先使用毫秒字段。
      var startMs = line.time_ms != null ? Number(line.time_ms || 0) : Number(line.t || line.time || 0) * 1000;
      // 下一行开始时间，用于推算当前行持续时间。
      var nextMs = lines[index + 1] ? (lines[index + 1].time_ms != null ? Number(lines[index + 1].time_ms || 0) : Number(lines[index + 1].t || lines[index + 1].time || 0) * 1000) : 0;
      // 当前行开始秒。
      var start = Math.max(0, startMs || 0) / 1000;
      // 下一行开始秒。
      var next = Math.max(0, nextMs || 0) / 1000;
      // 当前行显示文本，缺主文本时退回 secondary。
      var text = String(line.text || line.secondary || '');
      // 逐字歌词统一归一化为旧播放器字符时间结构。
      var characters = normalizeLyricCharacters(line.characters, 'ms');
      return {
        // 行开始时间。
        t: start,
        // 行文本。
        text: text,
        // 行持续时间，优先使用宿主持续时间，否则用下一行间隔。
        duration: line.duration_ms != null ? Math.max(0.4, Number(line.duration_ms || 0) / 1000) : Number(line.duration || (next > start ? next - start : 4.8)),
        // 逐字歌词数据。
        characters: characters,
        // 逐字模式下的字符总数。
        charCount: Math.max(1, characters.length ? characters[characters.length - 1].c1 : text.length),
        // 歌词来源标识。
        source: line.source || 'echo',
        // 保留宿主原始歌词行号，过滤占位行后仍能映射 current_index。
        sourceIndex: line.source_index != null ? Number(line.source_index) : index,
      };
    }).filter(function(line){ return line.text && !isNoLyricText(line.text); });
    // 是否存在可用的原生逐字时间。
    lyricsHasNativeKaraoke = lyricsLines.some(hasValidLyricCharacters);
    // 当前歌词时间来源。
    lyricsTimingSource = lyricsLines.length ? (lyricsHasNativeKaraoke ? 'echo-characters' : 'echo-line') : 'none';
    refreshBridgeLyricsSurface();
  }

  // 应用宿主播放队列快照。
  function applyQueue(snapshot) {
    // 队列签名只关心当前索引、数量和歌曲标识，减少相同队列反复重建面板和 3D 歌单架。
    // 宿主队列数组。
    var queue = Array.isArray(snapshot.queue) ? snapshot.queue : [];
    // 队列去重签名。
    var key = String(snapshot.currentQueueIndex == null ? '' : snapshot.currentQueueIndex) + '|' + queue.length + '|' + queue.map(function(song) {
      // 每首歌只取稳定标识和封面参与签名。
      return [
        String(song && (song.id || song.hash) || ''),
        bridgeSongCover(song)
      ].join(':');
    }).join(',');
    if (key === bridgeQueueKey) return;
    bridgeQueueKey = key;
    // 旧播放器主队列。
    playQueue = queue.map(normalizeBridgeSong);
    // 当前播放索引。
    currentIdx = Number(snapshot.currentQueueIndex);
    if (!isFinite(currentIdx) || currentIdx < 0 || currentIdx >= playQueue.length) {
      currentIdx = -1;
    }
    // 旧播放器歌单视图沿用同一份队列快照。
    playlist = playQueue.slice();
    if (typeof renderQueuePanel === 'function') renderQueuePanel({ scrollCurrent: true });
    if (typeof renderMiniQueuePanel === 'function') renderMiniQueuePanel({ scrollCurrent: true });
    if (typeof safeShelfRebuild === 'function') {
      try { safeShelfRebuild('echo-bridge', true); } catch (e) {}
    }
  }

  // 应用宿主完整播放快照。
  function applySnapshot(snapshot) {
    // 完整快照是桥接层的主入口：同步歌曲、队列、封面、播放模式、音量和首屏等待状态。
    if (!snapshot) return;
    // 宿主原始歌曲对象。
    var rawTrack = snapshot.track || null;
    // 是否有可展示的当前歌曲。
    var hasTrack = !!(rawTrack && (rawTrack.id || rawTrack.hash || rawTrack.name || rawTrack.title));
    // 合并本地乐观状态后的播放状态。
    var snapshotPlaying = resolveBridgePlaybackPlaying(snapshot.isPlaying);
    if (!hasTrack) snapshotPlaying = false;
    bridgeSnapshot = snapshot;
    bridgeSnapshot.isPlaying = snapshotPlaying;
    installAudioShim();
    forcePlayerSurface();

    // 归一化后的当前歌曲。
    var song = normalizeBridgeSong(rawTrack);
    // 当前歌曲总时长。
    var duration = Math.max(0, Number(snapshot.duration || song.duration || 0));
    // 当前歌曲播放位置，完整快照也可作为本地时钟锚点。
    var snapshotTime = Number(snapshot.currentTime);
    if (!isFinite(snapshotTime)) snapshotTime = bridgeCurrentTime();
    playing = hasTrack && snapshotPlaying;
    bridgePlaybackClock.time = Math.max(0, snapshotTime || 0);
    bridgePlaybackClock.duration = duration;
    bridgePlaybackClock.playing = playing;
    bridgePlaybackClock.rate = 1;
    bridgePlaybackClock.receivedAt = bridgeNow();
    audio.paused = !playing;
    audio.ended = false;
    audio.duration = duration;
    audio.playbackRate = 1;
    targetVolume = clamp01(snapshot.volume == null ? targetVolume : snapshot.volume);
    if (targetVolume > 0.01) lastNonZeroVolume = targetVolume;
    audio.volume = targetVolume;
    // 播放模式同步到旧播放器内部枚举。
    playMode = hostModeToMine(snapshot.playMode);

    applyQueue(snapshot);
    applyCover(hasTrack ? song : {});
    if (hasTrack) revealBridgeVisualSurface();

    // 初始提示节点。
    var hint = document.getElementById('hint');
    if (hint) hint.classList.add('hidden');
    // 缩略封面外层节点。
    var thumbWrap = document.getElementById('thumb-wrap');
    if (thumbWrap) thumbWrap.classList.toggle('visible', hasTrack && !!song.id);
    // 缩略曲名节点。
    var thumbTitle = document.getElementById('thumb-title');
    // 缩略歌手节点。
    var thumbArtist = document.getElementById('thumb-artist');
    if (hasTrack) {
      // 有歌曲时退出等待态并刷新控制条曲目信息。
      setBridgeWaitingState(false);
      if (thumbTitle) thumbTitle.textContent = song.name || '';
      if (thumbArtist) thumbArtist.textContent = song.artist || '';
      if (typeof updateControlTrackInfo === 'function') updateControlTrackInfo(song);
    } else {
      // 无歌曲时清空当前索引和缩略文本，展示等待宿主状态。
      currentIdx = -1;
      if (thumbTitle) thumbTitle.textContent = '';
      if (thumbArtist) thumbArtist.textContent = '';
      setBridgeWaitingState(true);
    }
    if (typeof updatePlayModeButton === 'function') updatePlayModeButton(false);
    if (typeof setPlayIcon === 'function') setPlayIcon(playing);
    if (typeof updatePlaybackProgressUi === 'function') updatePlaybackProgressUi();
    if (typeof updateVolumeUi === 'function') updateVolumeUi();
  }

  // 安装旧播放器控件的桥接拦截器。
  function installControlInterceptors() {
    // 拦截旧播放器控件事件，阻止它们执行本地播放逻辑，改为发送 EchoMusic 宿主命令。
    // 播放/暂停按钮。
    var playButton = document.getElementById('play-btn');
    if (playButton && !playButton.__echoBridgePlayBound) {
      playButton.__echoBridgePlayBound = true;
      playButton.onclick = null;
      playButton.addEventListener('click', function(e) {
        // 捕获阶段阻止旧点击处理器执行。
        e.preventDefault();
        e.stopPropagation();
        if (typeof e.stopImmediatePropagation === 'function') e.stopImmediatePropagation();
        toggleBridgePlayback();
      }, true);
    }

    // 播放进度条。
    var progress = document.getElementById('progress-bar');
    if (progress && !progress.__echoBridgeBound) {
      progress.__echoBridgeBound = true;
      // 根据指针事件位置计算并提交 seek。
      var seekFromEvent = function(e) {
        if (!bridgeSnapshot || !bridgeSnapshot.duration) return;
        // 进度条视口矩形。
        var rect = progress.getBoundingClientRect();
        // 指针所在比例。
        var ratio = clamp01((e.clientX - rect.left) / Math.max(1, rect.width));
        // 目标播放时间。
        var value = ratio * Number(bridgeSnapshot.duration || 0);
        setBridgeClockTime(value);
        bridgeSnapshot.currentTime = value;
        command('seek', { value: value });
      };
      progress.addEventListener('pointerdown', function(e) {
        // 拖动开始时立即 seek，并标记进度条处于拖动状态。
        e.preventDefault();
        e.stopPropagation();
        if (typeof e.stopImmediatePropagation === 'function') e.stopImmediatePropagation();
        progress.setPointerCapture && progress.setPointerCapture(e.pointerId);
        progress.classList.add('is-dragging');
        seekFromEvent(e);
      }, true);
      progress.addEventListener('pointermove', function(e) {
        // 只有拖动状态下才连续发送 seek。
        if (!progress.classList.contains('is-dragging')) return;
        e.preventDefault();
        e.stopPropagation();
        if (typeof e.stopImmediatePropagation === 'function') e.stopImmediatePropagation();
        seekFromEvent(e);
      }, true);
      progress.addEventListener('pointerup', function(e) {
        // 拖动结束时提交最后一次 seek。
        progress.classList.remove('is-dragging');
        e.preventDefault();
        e.stopPropagation();
        if (typeof e.stopImmediatePropagation === 'function') e.stopImmediatePropagation();
        seekFromEvent(e);
      }, true);
      progress.addEventListener('click', function(e) {
        // 普通点击进度条也走同一个 seek 逻辑。
        e.preventDefault();
        e.stopPropagation();
        if (typeof e.stopImmediatePropagation === 'function') e.stopImmediatePropagation();
        seekFromEvent(e);
      }, true);
    }

    // 音量滑块。
    var volume = document.getElementById('volume-slider');
    if (volume && !volume.__echoBridgeBound) {
      volume.__echoBridgeBound = true;
      volume.addEventListener('input', function(e) {
        // 滑动期间实时把音量交给宿主。
        e.stopPropagation();
        if (typeof e.stopImmediatePropagation === 'function') e.stopImmediatePropagation();
        command('volume', { value: Number(volume.value || 0) });
      }, true);
      volume.addEventListener('change', function(e) {
        // change 事件作为 input 的兜底提交。
        e.stopPropagation();
        if (typeof e.stopImmediatePropagation === 'function') e.stopImmediatePropagation();
        command('volume', { value: Number(volume.value || 0) });
      }, true);
    }

    // 提交桥接音量并同步本地 UI。
    function commitBridgeVolume(value) {
      // 归一化后的音量。
      var next = clamp01(value);
      targetVolume = next;
      if (next > 0.01) lastNonZeroVolume = next;
      if (typeof updateVolumeUi === 'function') updateVolumeUi();
      command('volume', { value: next });
    }

    // 静音按钮。
    var volumeButton = document.getElementById('volume-btn');
    if (volumeButton && !volumeButton.__echoBridgeMuteBound) {
      volumeButton.__echoBridgeMuteBound = true;
      volumeButton.addEventListener('click', function(e) {
        // 静音/恢复音量都走宿主音量命令。
        e.preventDefault();
        e.stopPropagation();
        if (typeof e.stopImmediatePropagation === 'function') e.stopImmediatePropagation();
        commitBridgeVolume(targetVolume > 0.01 ? 0 : (lastNonZeroVolume || 0.8));
      }, true);
    }

    // 音量控件外层，用于滚轮调节音量。
    var volumeWrap = document.getElementById('volume-control');
    if (volumeWrap && !volumeWrap.__echoBridgeWheelBound) {
      volumeWrap.__echoBridgeWheelBound = true;
      volumeWrap.addEventListener('wheel', function(e) {
        // 滚轮调节音量时保持音量面板打开。
        e.preventDefault();
        e.stopPropagation();
        if (typeof e.stopImmediatePropagation === 'function') e.stopImmediatePropagation();
        if (typeof keepVolumePanelOpen === 'function') keepVolumePanelOpen();
        commitBridgeVolume(targetVolumeAfterWheel(e));
      }, { capture: true, passive: false });
    }
  }

  // 覆盖原播放入口: 控件只驱动 EchoMusic 宿主播放器。
  // 播放/暂停入口覆盖为桥接播放切换。
  togglePlay = function() { toggleBridgePlayback(); };
  // 下一首入口覆盖为宿主下一首命令。
  nextTrack = function() { command('next'); };
  // 上一首入口覆盖为宿主上一首命令。
  prevTrack = function() { command('prev'); };
  // 播放模式循环入口覆盖为宿主模式切换命令。
  cyclePlayMode = function() { command('cycle-mode'); };
  // 队列点击播放入口覆盖为按索引播放宿主队列。
  playQueueAt = function(index) { command('play-index', { index: Number(index) || 0 }); };
  // 请求宿主把队列索引设为下一首。
  requestHostPlayNextIndex = function(index) { command('queue-play-next-index', { index: Number(index) || 0 }); };
  // 请求宿主把详情页歌曲加入下一首。
  queueDetailSongNext = function(song) {
    // 转成宿主命令可接受的歌曲结构。
    var payloadSong = hostCommandSong(song);
    if (!payloadSong) return;
    command('queue-play-next-song', { song: payloadSong });
    if (typeof showToast === 'function') showToast('已发送下一首: ' + (song.name || ''));
  };
  // 请求宿主直接播放指定歌曲。
  requestHostPlaySong = function(song) {
    // 转成宿主命令可接受的歌曲结构。
    var payloadSong = hostCommandSong(song);
    if (!payloadSong) return false;
    command('play-song', { song: payloadSong });
    return true;
  };
  // 随机播放入口覆盖为宿主随机模式命令。
  shuffleQueue = function() { command('set-mode', { mode: 'random' }); };
  // 清空队列入口覆盖为宿主清空队列命令。
  clearQueue = function() { command('queue-clear'); };
  // 移除队列歌曲入口覆盖为宿主按索引移除命令。
  removeFromQueue = function(index) { command('queue-remove-index', { index: Number(index) || 0 }); };
  // 歌词面板入口在桥接模式下只切换粒子歌词显示。
  toggleLyricsPanel = function() {
    if (typeof setParticleLyricsSilently === 'function') setParticleLyricsSilently(!fx.particleLyrics);
  };
  // 全屏入口覆盖为宿主窗口控制命令。
  toggleFullscreen = function() { command('window-control', { action: 'fullscreen' }); };

  // Esc 键关闭或返回宿主页面。
  window.addEventListener('keydown', function(e) {
    if (e.key === 'Escape') {
      // 阻止旧播放器或浏览器默认处理 Esc。
      e.preventDefault();
      e.stopPropagation();
      command('close');
    }
  }, true);

  // 接收 EchoMusic 宿主通过 postMessage 推送的桥接协议消息。
  window.addEventListener('message', function(event) {
    // 父页面消息分为初始化、完整快照、歌词、进度和频谱；频谱只更新缓存，实际消费在主循环。
    // 原始 message 数据。
    var data = event && event.data;
    if (!data || data.source !== BRIDGE_PARENT_SOURCE) return;
    if (data.type === 'echo-player-frontend:init') {
      // 初始化消息包含宿主窗口控制能力。
      bridgeHostControls = Object.assign(bridgeHostControls, (data.payload && data.payload.hostControls) || {});
      forcePlayerSurface();
      refreshBridgeViewport('echo-bridge-init');
      installWindowControls();
      // 初始化完成后主动索要一次完整快照。
      post('echo-player-frontend:request-snapshot');
    } else if (data.type === 'echo-player-frontend:snapshot') {
      // 完整快照同步当前歌曲、队列、音量和播放状态。
      applySnapshot(data.payload);
    } else if (data.type === 'echo-player-frontend:lyrics') {
      // 歌词消息只刷新歌词缓存和显示层。
      applyLyricsPayload(data.payload);
    } else if (data.type === 'echo-player-frontend:position') {
      // 位置消息事件驱动到达，更新播放时钟锚点。
      applyPositionPayload(data.payload);
    } else if (data.type === 'echo-player-frontend:spectrum') {
      // 频谱消息只写入宿主频谱帧，主循环下一帧再消费。
      var spectrum = data.payload || {};
      // 频率柱数据。
      bridgeSpectrum.bins = isHostSpectrumArray(spectrum.bins) ? spectrum.bins : [];
      // 波形数据。
      bridgeSpectrum.waveform = isHostSpectrumArray(spectrum.waveform) ? spectrum.waveform : [];
      // RMS 能量。
      bridgeSpectrum.rms = isFinite(Number(spectrum.rms)) ? clamp01(Number(spectrum.rms)) : 0;
      // 峰值能量。
      bridgeSpectrum.peak = isFinite(Number(spectrum.peak)) ? clamp01(Number(spectrum.peak)) : 0;
      // 频谱帧更新时间。
      bridgeSpectrum.updatedAt = bridgeNow();
    }
  });

  // 安装桥接专用样式。
  installBridgeStyle();
  // 初始化顺序很重要：先安装样式和伪 audio，再拦截控件、打开歌词、显示等待态，最后通知父页面 ready。
  // 安装返回按钮。
  installCloseButton();
  // 安装窗口控制按钮。
  installWindowControls();
  // 安装伪 audio。
  installAudioShim();
  // 安装控件拦截器。
  installControlInterceptors();
  // 默认开启歌词视觉。
  ensureBridgeLyricsEnabled();
  // 强制显示播放器表面。
  forcePlayerSurface();
  // 初始进入等待宿主歌曲状态。
  setBridgeWaitingState(true);
  setInterval(function() {
    // 部分旧 UI 会重建节点，定时补绑可保持桥接拦截持续有效。
    forcePlayerSurface();
    installControlInterceptors();
  }, 1000);
  // 通知宿主 iframe 已就绪。
  post('echo-player-frontend:ready');
})();
// 启动主循环。
startMainLoopSafely();
