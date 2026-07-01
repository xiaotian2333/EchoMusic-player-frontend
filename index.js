// 这个入口文件只负责 EchoMusic 宿主侧的桥接：
// 1. 在歌词视图打开时挂载全屏覆盖层。
// 2. 通过 iframe 加载插件内置的播放器页面。
// 3. 在宿主播放器状态、歌词、频谱数据和 iframe 页面之间转发消息。
const LEGACY_PAGE_PATH = '/main/plugin/player-frontend/player'
const FALLBACK_PATH = '/main/home'

// 宿主播放器的播放模式顺序，用于 iframe 请求“切换模式”时循环到下一项。
const playModeOrder = ['sequential', 'list', 'random', 'single']

// 兼容旧版插件路由：如果用户还停留在旧页面地址，后续会重定向回首页并改用覆盖层。
function isLegacyPluginPlayerPath(path) {
  return String(path || '').startsWith(LEGACY_PAGE_PATH)
}

// 从宿主路由对象中提取当前路径，兼容 fullPath 和 path 两种字段。
function getRoutePath(ctx) {
  const route = ctx?.router?.currentRoute?.value
  return String(route?.fullPath || route?.path || '')
}

// 将插件目录和相对片段拼成宿主文件系统可以识别的插件内路径。
function getPluginFilePath(ctx, ...parts) {
  const root = String(ctx?.descriptor?.directory || '').replace(/[\\/]+$/, '')
  return [root, ...parts].filter(Boolean).join('/')
}

// 统一处理外部字段：空值、null、undefined 和纯空白文本都落到 fallback。
function text(value, fallback = '') {
  const resolved = String(value ?? '').trim()
  return resolved || fallback
}

// 不同来源的歌曲对象字段名不一致，这里提取最适合展示的标题。
function trackTitle(track) {
  return text(track?.title || track?.name || track?.songname, '未知歌曲')
}

// 提取歌手名，优先使用扁平字段，再兼容 artists/singers 数组。
function trackArtist(track) {
  if (typeof track?.artist === 'string' && track.artist.trim()) return track.artist
  if (typeof track?.author === 'string' && track.author.trim()) return track.author
  const names = [
    ...(Array.isArray(track?.artists) ? track.artists : []),
    ...(Array.isArray(track?.singers) ? track.singers : []),
  ]
    .map((item) => item?.name || item)
    .filter(Boolean)
  return names.length ? names.join(' / ') : '未知歌手'
}

// 提取封面地址，兼容宿主、队列和外部命令可能传入的不同字段名。
function trackCover(track) {
  return text(
    track?.coverUrl ||
      track?.cover ||
      track?.picUrl ||
      track?.albumCover ||
      track?.albumImg ||
      track?.img ||
      track?.image ||
      track?.cover_url,
  )
}

// 将宿主歌曲对象压成 iframe 页面需要的稳定结构，避免子页面直接依赖宿主内部字段。
function normalizeSong(song) {
  if (!song) return null
  return {
    id: String(song.id ?? song.trackId ?? song.hash ?? ''),
    hash: String(song.hash ?? song.id ?? ''),
    name: trackTitle(song),
    title: trackTitle(song),
    artist: trackArtist(song),
    cover: trackCover(song),
    coverUrl: trackCover(song),
    album: text(song.album || song.albumName),
    duration: Number(song.duration || 0),
  }
}

// 根据宿主歌词设置选择翻译或罗马音作为副歌词。
function lyricSecondary(ctx, line) {
  const lyricStore = ctx.stores.lyric
  if (!line) return ''
  if (typeof lyricStore.lineSecondaryText === 'function') return lyricStore.lineSecondaryText(line)
  if (lyricStore.showTranslation && line.translated) return line.translated
  if (lyricStore.showRomanization && line.romanized) return line.romanized
  return ''
}

// 归一化逐字歌词时间轴；异常时间会被钳回 0，空文本字符会被丢弃。
function lyricCharacters(line) {
  const characters = Array.isArray(line?.characters) ? line.characters : []
  return characters
    .map((character) => {
      const startTime = Number(character?.startTime ?? 0)
      const endTime = Number(character?.endTime ?? character?.startTime ?? 0)
      return {
        text: String(character?.text ?? ''),
        startTime: Number.isFinite(startTime) ? startTime : 0,
        endTime: Number.isFinite(endTime) ? endTime : 0,
      }
    })
    .filter((character) => character.text)
}

// 将宿主以秒为单位的歌词行转换为 iframe 使用的毫秒结构，并推算当前行持续时间。
function normalizeLyricLine(ctx, line, index, lines) {
  const startMs = Math.max(0, Math.round(Number(line?.time || 0) * 1000))
  const nextStartMs = Math.max(0, Math.round(Number(lines[index + 1]?.time || 0) * 1000))
  return {
    time_ms: startMs,
    text: text(line?.text),
    secondary: lyricSecondary(ctx, line),
    characters: lyricCharacters(line),
    duration_ms: nextStartMs > startMs ? Math.max(400, nextStartMs - startMs) : 4800,
  }
}

// 创建真正承载 iframe 的覆盖层组件。组件内部维护宿主状态快照、消息桥和资源清理逻辑。
function createPlayerFrame(ctx, closeOverlay) {
  const { defineComponent, h, ref, onMounted, onBeforeUnmount } = ctx.vue

  return defineComponent({
    name: 'PlayerFrontendBridgeFrame',
    setup() {
      const iframeRef = ref(null)
      const iframeSrc = ref('')
      const loadError = ref('')
      let ready = false
      let disposed = false
      let lastLyricsKey = ''
      let lastSpectrumFrame = null
      let spectrumDispose = null
      let lyricStoreUnsub = null
      let lastLyricStoreKey = ''
      let stopTrackWatch = null
      let stopVolumeWatch = null
      let stopFontWatch = null
      let commandQueue = Promise.resolve()
      // 位置心跳定时器，每 5 秒向 iframe 推送一次当前进度，防止长时间播放后时钟漂移。
      let positionHeartbeatTimer = null

      // 所有发往 iframe 的消息都带上固定 source，子页面据此区分宿主消息和其他窗口消息。
      const postToFrame = (payload) => {
        const target = iframeRef.value?.contentWindow
        if (!target) return
        target.postMessage(
          {
            ...payload,
            source: 'echo-player-frontend-parent',
          },
          '*',
        )
      }

      // 主动队列可能来自响应式 ref、方法或 store 字段，这里统一取出队列 id、当前项和歌曲列表。
      const getQueueState = () => {
        const activeQueue =
          ctx.playlist.activeQueue?.value ||
          ctx.playlist.getActiveQueue?.() ||
          ctx.stores.playlist.activeQueue ||
          null
        const songs = Array.isArray(activeQueue?.songs) ? activeQueue.songs : []
        return {
          queueId: activeQueue?.id ?? ctx.stores.playlist.activeQueueId ?? null,
          currentTrackId: activeQueue?.currentTrackId ?? null,
          songs,
        }
      }

      // 打开覆盖层时确保当前歌曲歌词已加载；已加载同 hash 的歌词则直接复用。
      const ensureLyricLoaded = () => {
        const track = ctx.player.currentTrack.value || ctx.stores.player.currentTrackSnapshot
        const hash = String(
          track?.hash || track?.id || ctx.stores.player.currentTrackId || '',
        ).trim()
        if (!hash) return
        if (
          ctx.stores.lyric.loadedHash === hash &&
          (ctx.stores.lyric.lines.length || ctx.stores.lyric.rawLyric)
        ) {
          return
        }
        void ctx.stores.lyric.fetchLyrics?.(hash, {
          preserveCurrent: true,
          track,
          duration: ctx.stores.player.duration ? ctx.stores.player.duration * 1000 : undefined,
          albumAudioId: track?.albumAudioId || track?.mixSongId,
        })
      }

      // 构造歌词 payload，并生成内容 key，用于避免重复向 iframe 推送相同歌词。
      const buildLyricsPayload = () => {
        const player = ctx.stores.player
        const lyric = ctx.stores.lyric
        const current = normalizeSong(ctx.player.currentTrack.value || player.currentTrackSnapshot)
        const currentId = String(player.currentTrackId ?? current?.id ?? '')
        const hash = String(current?.hash || currentId || '').trim()
        const loadedHash = String(lyric.loadedHash || '').trim()
        const sourceLines =
          hash && loadedHash === hash && Array.isArray(lyric.lines) ? lyric.lines : []
        const lines = sourceLines
          .map((line, index) => normalizeLyricLine(ctx, line, index, sourceLines))
          .filter((line) => line.text)
        const key = [
          currentId,
          hash,
          loadedHash,
          lines
            .map((line) =>
              [
                line.time_ms,
                line.text,
                line.secondary,
                line.characters
                  .map((character) =>
                    [character.text, character.startTime, character.endTime].join(','),
                  )
                  .join(';'),
              ].join(':'),
            )
            .join('|'),
        ].join('::')

        return {
          key,
          track_id: currentId,
          hash,
          lines,
          tips: lyric.isLoading ? '歌词加载中...' : lyric.tips || '',
        }
      }

      // 构造位置 payload，直接读取宿主当前时间（事件驱动，无需锚点外推）。
      const buildPositionPayload = (cause) => {
        const player = ctx.stores.player
        return {
          position_ms: Math.max(0, Math.round(Number(player.currentTime || 0) * 1000)),
          duration_ms: Math.max(0, Math.round(Number(player.duration || 0) * 1000)),
          is_playing: Boolean(player.isPlaying),
          cause: cause || 'tick',
        }
      }

      // 汇总 iframe 首屏和常规刷新所需的完整播放器快照。
      const buildSnapshot = () => {
        const player = ctx.stores.player
        const lyric = ctx.stores.lyric
        const current = normalizeSong(ctx.player.currentTrack.value || player.currentTrackSnapshot)
        const queueState = getQueueState()
        const queue = queueState.songs.map(normalizeSong).filter(Boolean)
        const currentId = String(player.currentTrackId ?? current?.id ?? '')
        const currentQueueTrackId = String(queueState.currentTrackId ?? currentId)
        const currentQueueIndex = queue.findIndex((song) => String(song.id) === currentQueueTrackId)

        return {
          track: current,
          currentTrackId: currentId,
          currentQueueIndex,
          queue,
          queueId: queueState.queueId,
          isPlaying: Boolean(player.isPlaying),
          currentTime: Number(player.currentTime || 0),
          duration: Number(player.duration || current?.duration || 0),
          volume: Number(player.volume ?? 0.8),
          playMode: String(player.playMode || 'list'),
          lyric: {
            currentIndex: Number(lyric.currentIndex ?? -1),
            tips: lyric.isLoading ? '歌词加载中...' : lyric.tips || '',
          },
        }
      }

      // 从主程序设置读取页面歌词字体，iframe 内的舞台歌词始终跟随这个字体族。
      const buildAppearancePayload = () => {
        const settings = ctx.stores.settings || ctx.settings
        let lyricFontFamily = ''
        try {
          if (typeof settings?.buildLyricFontFamily === 'function') {
            lyricFontFamily = settings.buildLyricFontFamily()
          }
        } catch (error) {
          console.warn('[PlayerFrontendBridge] 读取歌词字体失败', error)
        }
        return {
          lyricFontFamily: String(lyricFontFamily || '').trim(),
        }
      }

      // 把宿主窗口能力暴露给 iframe，子页面据此决定是否显示全屏、小窗等按钮。
      const buildHostControlsPayload = () => ({
        platform: String(window.electron?.platform || ''),
        showFullscreenButton:
          (ctx.stores.settings || ctx.settings)?.showFullscreenButton !== false,
        canShowMiniPlayer: typeof window.electron?.miniPlayer?.show === 'function',
      })

      // 推送歌词，仅事件驱动（歌词内容变更时调用），不再定时轮询。
      const pushLyrics = (force = false) => {
        if (!ready && !force) return
        ensureLyricLoaded()
        const payload = buildLyricsPayload()
        if (!force && payload.key === lastLyricsKey) return
        lastLyricsKey = payload.key
        postToFrame({
          type: 'echo-player-frontend:lyrics',
          payload,
        })
      }

      // 事件驱动的位置推送（取代轮询），仅在关键时机或低频心跳时发送。
      const pushPosition = (cause) => {
        if (!ready) return
        postToFrame({
          type: 'echo-player-frontend:position',
          payload: buildPositionPayload(cause),
        })
      }

      // 推送主程序外观设置，例如页面歌词字体。
      const pushAppearance = (force = false) => {
        if (!ready && !force) return
        postToFrame({
          type: 'echo-player-frontend:appearance',
          payload: buildAppearancePayload(),
        })
      }

      // 推送完整快照，仅在曲目切换或命令完成后调用。
      const pushSnapshot = (force = false) => {
        if (!ready && !force) return
        ensureLyricLoaded()
        postToFrame({
          type: 'echo-player-frontend:snapshot',
          payload: buildSnapshot(),
        })
      }

      // 订阅歌词 store，仅在歌词内容（lines/loadedHash）变化时推送给 iframe。
      const initLyricStoreSubscription = () => {
        if (lyricStoreUnsub) return
        const lyricStore = ctx.stores.lyric
        const buildStoreKey = (state) =>
          [
            Array.isArray(state?.lines) ? state.lines.length : 0,
            String(state?.loadedHash || ''),
            Boolean(state?.isLoading) ? '1' : '0',
            String(state?.tips || ''),
          ].join('::')
        lastLyricStoreKey = buildStoreKey(lyricStore)
        if (typeof lyricStore.$subscribe === 'function') {
          lyricStoreUnsub = lyricStore.$subscribe((mutation, state) => {
            const nextKey = buildStoreKey(state)
            if (nextKey === lastLyricStoreKey) return
            lastLyricStoreKey = nextKey
            pushLyrics(false)
          })
        }
      }

      // 监听曲目切换，事件驱动方式推送快照、歌词和位置。
      const initTrackWatch = () => {
        const getTrackId = () => {
          const player = ctx.stores.player
          const current = ctx.player.currentTrack.value || player.currentTrackSnapshot
          return String(current?.id || current?.hash || player.currentTrackId || '')
        }
        let lastId = getTrackId()
        stopTrackWatch = ctx.vue.watch(
          getTrackId,
          (newId) => {
            if (!newId || newId === lastId) return
            lastId = newId
            pushSnapshot(true)
            pushLyrics(true)
            pushPosition('track_change')
          },
        )
      }

      // 监听主程序音量变更，同步推快照更新 iframe 侧音量滑块和音频。
      const initVolumeWatch = () => {
        stopVolumeWatch = ctx.vue.watch(
          () => Number(ctx.stores.player.volume ?? 0.8),
          () => {
            if (!ready || disposed) return
            pushSnapshot(true)
          },
        )
      }

      // 监听主程序字体设置变化，同步刷新 iframe 内 canvas 歌词纹理。
      const initFontWatch = () => {
        if (stopFontWatch) return
        const settings = ctx.stores.settings || ctx.settings
        stopFontWatch = ctx.vue.watch(
          () => [
            String(settings?.lyricFont || ''),
            String(settings?.globalFont || ''),
            buildAppearancePayload().lyricFontFamily,
          ].join('::'),
          () => {
            if (!ready || disposed) return
            pushAppearance(true)
          },
        )
      }

      // 位置心跳：每 5 秒推送一次当前进度，防止 iframe 本地时钟长时间漂移。
      const startPositionHeartbeat = () => {
        clearInterval(positionHeartbeatTimer)
        positionHeartbeatTimer = setInterval(() => {
          if (!ready || disposed) return
          pushPosition('tick')
        }, 5000)
      }

      // 停止位置心跳。
      const stopPositionHeartbeat = () => {
        clearInterval(positionHeartbeatTimer)
        positionHeartbeatTimer = null
      }

      // 按固定顺序循环播放模式，供 iframe 的模式按钮调用。
      const cyclePlayMode = () => {
        const mode = String(ctx.stores.player.playMode || 'list')
        const index = playModeOrder.indexOf(mode)
        ctx.player.setPlayMode(playModeOrder[(index + 1) % playModeOrder.length])
      }

      // 从当前播放队列中安全取出指定索引的歌曲，非法索引或无效歌曲会返回 null。
      const getQueueSongAt = (index) => {
        const normalizedIndex = Number(index)
        if (!Number.isInteger(normalizedIndex) || normalizedIndex < 0) return null
        const queueState = getQueueState()
        const song = queueState.songs[normalizedIndex]
        if (!song?.id && !song?.hash) return null
        return { queueState, song }
      }

      // 队列相关命令需要携带 queueId；没有活动队列时让宿主使用默认行为。
      const queueOptions = (queueState) =>
        queueState?.queueId == null ? undefined : { queueId: queueState.queueId }

      // 归一化 iframe 传回的歌曲对象，补齐宿主播放命令依赖的 id/hash/audioUrl 等字段。
      const commandSong = (song) => {
        const source = song || {}
        const normalized = normalizeSong(source)
        if (!normalized?.id && !normalized?.hash) return null
        return {
          ...source,
          ...normalized,
          id: String(source.id ?? source.trackId ?? source.hash ?? normalized.id ?? ''),
          hash: text(source.hash || normalized.hash || normalized.id),
          audioUrl: text(source.audioUrl || source.url),
          mixSongId: source.mixSongId ?? source.mixsongid ?? 0,
        }
      }

      // 按队列索引播放，保留完整队列上下文，确保宿主能继续处理上一首/下一首。
      const playQueueIndex = async (index) => {
        const target = getQueueSongAt(index)
        if (!target) return
        const { queueState, song } = target
        const trackId = song.id || song.hash
        if (!trackId) return
        await ctx.player.playTrack(trackId, {
          playlist: queueState.songs,
          sourceQueueId: queueState.queueId,
        })
      }

      // 播放 iframe 直接传入的歌曲对象。
      const playCommandSong = async (song) => {
        const target = commandSong(song)
        if (!target) return
        await ctx.player.playSong(target)
      }

      // 将 iframe 传入的歌曲插入下一首播放。
      const playNextCommandSong = async (song) => {
        const target = commandSong(song)
        if (!target) return
        await ctx.player.playNext(target)
      }

      // 将当前队列中的某一项插入下一首。
      const playNextQueueIndex = async (index) => {
        const target = getQueueSongAt(index)
        if (!target) return
        await ctx.player.playNext(target.song, queueOptions(target.queueState))
      }

      // 从当前队列移除指定索引的歌曲。
      const removeQueueIndex = async (index) => {
        const target = getQueueSongAt(index)
        if (!target) return
        const trackId = target.song.id || target.song.hash
        if (!trackId) return
        await ctx.playlist.remove(trackId, target.queueState.queueId)
      }

      // 清空当前活动队列。
      const clearQueue = async () => {
        const queueState = getQueueState()
        await ctx.playlist.clear(queueState.queueId)
      }

      // 接收 iframe 指定的播放模式，只有宿主支持的模式会被应用。
      const setPlayMode = (mode) => {
        const normalized = String(mode || '')
        if (!playModeOrder.includes(normalized)) return
        ctx.player.setPlayMode(normalized)
      }

      // iframe 的所有控制请求最终都汇聚到这里，再映射到 EchoMusic 宿主 API。
      const executeCommand = async (data) => {
        if (data.command === 'toggle-play') await ctx.player.toggle()
        else if (data.command === 'play') {
          if (!ctx.stores.player.isPlaying) await ctx.player.toggle()
        } else if (data.command === 'pause') {
          if (ctx.stores.player.isPlaying) await ctx.player.toggle()
        } else if (data.command === 'prev') await ctx.player.prev()
        else if (data.command === 'next') await ctx.player.next()
        else if (data.command === 'seek') ctx.player.seek(Math.max(0, Number(data.value) || 0))
        else if (data.command === 'volume') {
          ctx.player.setVolume(Math.max(0, Math.min(1, Number(data.value) || 0)))
        } else if (data.command === 'cycle-mode') cyclePlayMode()
        else if (data.command === 'play-index') await playQueueIndex(Number(data.index))
        else if (data.command === 'play-song') await playCommandSong(data.song)
        else if (data.command === 'queue-play-next-song') await playNextCommandSong(data.song)
        else if (data.command === 'queue-play-next-index') await playNextQueueIndex(Number(data.index))
        else if (data.command === 'queue-remove-index') await removeQueueIndex(Number(data.index))
        else if (data.command === 'queue-clear') await clearQueue()
        else if (data.command === 'set-mode') setPlayMode(data.mode)
        else if (data.command === 'close') closeOverlay()
        else if (data.command === 'mini-player') void window.electron?.miniPlayer?.show?.()
        else if (data.command === 'window-control') {
          const action = String(data.action || '')
          if (['minimize', 'fullscreen', 'maximize', 'close'].includes(action)) {
            window.electron?.windowControl?.(action)
          }
        }
      }

      // 命令完成或失败后都主动补发状态，确保 iframe 不会停留在乐观 UI 状态。
      const pushCommandResultState = () => {
        if (disposed) return
        pushSnapshot(true)
        pushPosition('command')
      }

      // 用 Promise 队列串行执行 iframe 命令，避免连续点击导致播放、队列操作交叉执行。
      const handleCommand = (data) => {
        commandQueue = commandQueue
          .catch(() => {})
          .then(async () => {
            await executeCommand(data)
            pushCommandResultState()
          })
          .catch((error) => {
            console.warn('[PlayerFrontendBridge] 命令执行失败', error)
            pushCommandResultState()
          })
      }

      // 处理来自 iframe 的握手、命令和主动刷新请求；source 校验用于隔离其他窗口消息。
      const handleMessage = (event) => {
        const data = event?.data
        if (!data || data.source !== 'echo-player-frontend-child') return

        switch (data.type) {
          case 'echo-player-frontend:ready':
            ready = true
            postToFrame({
              type: 'echo-player-frontend:init',
              payload: {
                directEnter: true,
                pluginVersion: String(ctx.manifest?.version || ''),
                hostControls: buildHostControlsPayload(),
                appearance: buildAppearancePayload(),
              },
            })
            pushSnapshot(true)
            pushLyrics(true)
            pushPosition('init')
            if (lastSpectrumFrame) {
              postToFrame({
                type: 'echo-player-frontend:spectrum',
                payload: lastSpectrumFrame,
              })
            }
            break
          case 'echo-player-frontend:command':
            handleCommand(data)
            break
          case 'echo-player-frontend:request-snapshot':
            pushSnapshot(true)
            pushLyrics(true)
            pushAppearance(true)
            pushPosition('init')
            break
        }
      }

      // Escape 始终关闭覆盖层，并阻止事件继续传给底层页面。
      const handleKeydown = (event) => {
        if (event.key !== 'Escape') return
        event.preventDefault()
        event.stopPropagation()
        closeOverlay()
      }

      // 通过宿主文件系统 API 获取插件内播放器页面地址，避免硬编码本地文件协议。
      const loadFrame = async () => {
        const result = await ctx.fs.getFileUrl(getPluginFilePath(ctx, 'player-frontend', 'index.html'))
        if (disposed) return
        if (!result?.ok || !result.url) {
          loadError.value = result?.error || '原播放器页面加载失败'
          return
        }
        iframeSrc.value = result.url
      }

      onMounted(() => {
        // 挂载期间标记 body，便于全局样式处理覆盖层打开时的滚动和层级。
        document.body.classList.add('epf-overlay-open')
        window.addEventListener('message', handleMessage)
        window.addEventListener('keydown', handleKeydown, true)
        void loadFrame()
        initLyricStoreSubscription()
        initTrackWatch()
        initVolumeWatch()
        initFontWatch()
        startPositionHeartbeat()

        try {
          // 订阅宿主音频频谱并转发给 iframe，用于驱动可视化；失败时静默降级为无频谱。
          spectrumDispose = ctx.audio.spectrum.subscribe(
            { fps: 24, binCount: 64, smoothing: 0.82, scale: 'mel', includeWaveform: true },
            (frame) => {
              lastSpectrumFrame = {
                bins: Array.isArray(frame?.bins) ? frame.bins : [],
                waveform: Array.isArray(frame?.waveform) ? frame.waveform : [],
                rms: Number(frame?.rms || 0),
                peak: Number(frame?.peak || 0),
                state: frame?.state || 'idle',
                timePos: frame?.timePos,
              }
              postToFrame({
                type: 'echo-player-frontend:spectrum',
                payload: lastSpectrumFrame,
              })
            },
          )
        } catch {
          spectrumDispose = null
        }
      })

      onBeforeUnmount(() => {
        // 组件销毁时撤销所有宿主侧副作用，避免后台继续推送消息或保留音频订阅。
        disposed = true
        ready = false
        document.body.classList.remove('epf-overlay-open')
        window.removeEventListener('message', handleMessage)
        window.removeEventListener('keydown', handleKeydown, true)
        stopPositionHeartbeat()
        if (lyricStoreUnsub) lyricStoreUnsub()
        lyricStoreUnsub = null
        if (stopTrackWatch) stopTrackWatch()
        stopTrackWatch = null
        if (stopVolumeWatch) stopVolumeWatch()
        stopVolumeWatch = null
        if (stopFontWatch) stopFontWatch()
        stopFontWatch = null
        if (spectrumDispose) spectrumDispose()
        spectrumDispose = null
      })

      // iframe 地址尚未就绪或加载失败时显示轻量占位，并保留关闭入口。
      const renderLoading = () =>
        h('div', { class: 'epf-bridge-loading' }, [
          h('div', { class: 'epf-bridge-loading-text' }, loadError.value || '正在加载插件播放器...'),
          h(
            'button',
            {
              class: 'epf-bridge-close',
              type: 'button',
              onClick: closeOverlay,
            },
            '关闭',
          ),
        ])

      // 覆盖层使用 dialog 语义；真正的播放器界面由 iframe 内的旧前端页面负责渲染。
      return () =>
        h(
          'div',
          {
            class: 'epf-bridge-page',
            role: 'dialog',
            'aria-modal': 'true',
          },
          [
            h('div', { class: 'epf-bridge-drag-strip' }),
            iframeSrc.value
              ? h('iframe', {
                  ref: iframeRef,
                  class: 'epf-bridge-frame',
                  src: iframeSrc.value,
                  allow: 'autoplay; fullscreen',
                  onLoad: () => {
                    ready = true
                    pushSnapshot(true)
                  },
                })
              : renderLoading(),
          ],
        )
    },
  })
}

// 外层组件只根据 overlayOpen 控制 iframe 宿主组件是否存在。
function createPlayerOverlay(ctx, overlayOpen, closeOverlay) {
  const { defineComponent, h } = ctx.vue
  const PlayerFrame = createPlayerFrame(ctx, closeOverlay)

  return defineComponent({
    name: 'PlayerFrontendOverlayHost',
    setup() {
      return () => (overlayOpen.value ? h(PlayerFrame) : null)
    },
  })
}

// 插件激活入口：注册覆盖层、监听歌词视图开关，并迁移旧路由入口。
export function activate(ctx) {
  const overlayOpen = ctx.vue.ref(false)

  // 关闭覆盖层时同步关闭宿主歌词视图，避免宿主状态仍认为歌词页处于打开状态。
  const closeOverlay = () => {
    overlayOpen.value = false
    if (ctx.stores.player.isLyricViewOpen) ctx.player.toggleLyricView(false)
  }

  // 打开覆盖层时同样收起宿主原生歌词视图，让自定义播放器接管展示。
  const openOverlay = () => {
    overlayOpen.value = true
    if (ctx.stores.player.isLyricViewOpen) ctx.player.toggleLyricView(false)
  }

  // 将覆盖层传送到宿主 UI 根节点，由宿主负责生命周期和层级挂载。
  ctx.ui.teleport(createPlayerOverlay(ctx, overlayOpen, closeOverlay), {
    id: 'player-frontend-overlay',
    className: 'epf-overlay-host',
  })

  // 宿主歌词视图被打开时改为展示自定义覆盖层。
  const stopLyricWatch = ctx.vue.watch(
    () => ctx.stores.player.isLyricViewOpen,
    (open) => {
      if (!open) return
      openOverlay()
    },
    { immediate: true, flush: 'sync' },
  )

  // 老版本插件页面不再直接渲染，命中旧路由时回到首页并通过覆盖层打开播放器。
  const stopLegacyRouteWatch = ctx.vue.watch(
    () => getRoutePath(ctx),
    (path) => {
      if (!isLegacyPluginPlayerPath(path)) return
      ctx.router.replace(FALLBACK_PATH).catch(() => {})
    },
    { immediate: true },
  )

  // 跟随插件卸载释放 watcher，并关闭可能仍然打开的覆盖层。
  ctx.dispose(() => {
    stopLyricWatch()
    stopLegacyRouteWatch()
    closeOverlay()
  })
}

// 当前插件没有额外的停用逻辑，清理工作已注册到 ctx.dispose。
export function deactivate() {}
