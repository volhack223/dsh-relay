#!/usr/bin/env node
/**
 * Self-Hosted DSH Remote Relay Server (Zero-Dependency Pure Node.js >= 18)
 * Wire-compatible with `dsh-go` ("自建服务器"), `ds-harness-remote` HostPluginRuntime,
 * and DSH Remote Protocol v1 (REST + WSS Control / Noise_IK Relay / WebRTC Signaling).
 */
import { createServer } from 'node:http'
import { createHash, createHmac, randomBytes, randomUUID, scryptSync, timingSafeEqual } from 'node:crypto'
import { existsSync, mkdirSync, readFileSync, renameSync, writeFileSync } from 'node:fs'
import { dirname, join, resolve } from 'node:path'
import { fileURLToPath } from 'node:url'

const __dirname = dirname(fileURLToPath(import.meta.url))

// ---------------------------------------------------------------------------
// 1. Minimal .env loader (works on Node 18 / 20 / 22 / 24 without --env-file)
// ---------------------------------------------------------------------------
function loadEnvFile(envPath) {
  if (!existsSync(envPath)) return
  const lines = readFileSync(envPath, 'utf8').split(/\r?\n/)
  for (const raw of lines) {
    const line = raw.trim()
    if (!line || line.startsWith('#')) continue
    const eq = line.indexOf('=')
    if (eq <= 0) continue
    const key = line.slice(0, eq).trim()
    let val = line.slice(eq + 1).trim()
    if ((val.startsWith('"') && val.endsWith('"')) || (val.startsWith("'") && val.endsWith("'"))) {
      val = val.slice(1, -1)
    }
    if (process.env[key] === undefined) process.env[key] = val
  }
}

// ---------------------------------------------------------------------------
// 2. Constants & Helpers
// ---------------------------------------------------------------------------
const PROTOCOL_VERSION = 1
const MAX_CONTROL_FRAME_BYTES = 64 * 1024
const MAX_RELAY_FRAME_BYTES = 1024 * 1024
const SERVER_SHUTDOWN_CLOSE_CODE = 1001
const SERVER_SHUTDOWN_CLOSE_REASON = 'SERVER_SHUTDOWN'
const SUPPORTED_TRANSPORTS = ['transport.lan', 'transport.p2p', 'transport.turn', 'transport.relay']
const TRANSPORT_NAMES = ['lan', 'p2p', 'turn', 'relay']

class ApiError extends Error {
  constructor(code, status = 400) {
    super(code)
    this.code = code
    this.status = status
  }
}

const sha256Hex = (v) => createHash('sha256').update(v).digest('hex')
const randomSecret = () => randomBytes(32).toString('base64url')
const constEqual = (a, b) => timingSafeEqual(Buffer.from(sha256Hex(a)), Buffer.from(sha256Hex(b)))

function createControlFrame(type, payload) {
  return { v: PROTOCOL_VERSION, id: randomUUID(), type, timestamp: Date.now(), payload }
}

function deriveSuccessor(token, nonce, deviceId) {
  const derive = (kind) =>
    createHmac('sha256', token)
      .update(JSON.stringify(['ds-harness-remote/refresh/v1', deviceId, nonce, kind]))
      .digest('base64url')
  return { accessToken: derive('access'), refreshToken: derive('refresh') }
}

// ---------------------------------------------------------------------------
// 3. Persistent Single-Account Store
// ---------------------------------------------------------------------------
export class RelayStore {
  constructor(file, account, password) {
    this.file = file
    this.account = account
    this.onInvalidate = () => {}
    let previous
    if (existsSync(file)) {
      try {
        previous = JSON.parse(readFileSync(file, 'utf8'))
      } catch {
        previous = undefined
      }
    }
    const salt = previous?.salt ?? randomSecret()
    const verifier = scryptSync(password, salt, 32).toString('hex')
    this.state = previous?.version === 1
      ? previous
      : { version: 1, account, salt, verifier, devices: {}, tokens: {} }
    if (this.state.account !== account) this.state.devices = {}
    if (this.state.account !== account || !constEqual(this.state.verifier, verifier)) {
      this.state.tokens = {}
    }
    this.state.account = account
    this.state.salt = salt
    this.state.verifier = verifier
    this.save()
  }

  save() {
    mkdirSync(dirname(this.file), { recursive: true })
    const tmp = `${this.file}.tmp`
    writeFileSync(tmp, JSON.stringify(this.state, null, 2), { mode: 0o600 })
    renameSync(tmp, this.file)
  }

  get(id) {
    const d = Object.hasOwn(this.state.devices, id) ? this.state.devices[id] : undefined
    if (!d) throw new ApiError('DEVICE_NOT_FOUND', 404)
    if (d.revoked) throw new ApiError('DEVICE_REVOKED', 403)
    return d
  }

  list() {
    return Object.values(this.state.devices).filter((d) => !d.revoked)
  }

  register(descriptor) {
    if (!descriptor || typeof descriptor.deviceId !== 'string' || !descriptor.deviceId) {
      throw new ApiError('INVALID_MESSAGE', 400)
    }
    if (descriptor.role !== 'host' && descriptor.role !== 'client') {
      throw new ApiError('INVALID_MESSAGE', 400)
    }
    if (typeof descriptor.identityKey !== 'string' || descriptor.identityKey.length !== 43) {
      throw new ApiError('INVALID_MESSAGE', 400)
    }
    const old = this.state.devices[descriptor.deviceId]
    if (old?.revoked) throw new ApiError('DEVICE_REVOKED', 403)
    if (old && (old.descriptor.identityKey !== descriptor.identityKey || old.descriptor.role !== descriptor.role)) {
      throw new ApiError('PEER_IDENTITY_MISMATCH', 409)
    }
    this.state.devices[descriptor.deviceId] = {
      descriptor: {
        deviceId: descriptor.deviceId,
        name: String(descriptor.name || 'Device').slice(0, 128),
        role: descriptor.role,
        platform: String(descriptor.platform || 'unknown').slice(0, 64),
        identityKey: descriptor.identityKey,
        clientVersion: String(descriptor.clientVersion || '0.6.7').slice(0, 64),
        ...(descriptor.role === 'host' && descriptor.harnessVersion
          ? { harnessVersion: String(descriptor.harnessVersion).slice(0, 64) }
          : {}),
      },
      revoked: false,
      lastSeenAt: old?.lastSeenAt ?? 0,
    }
    this.invalidate(descriptor.deviceId)
    return this.issue(descriptor.deviceId)
  }

  issue(deviceId, refreshTokenExpiresAt = Date.now() + 30 * 86400_000, previous) {
    const tokens = { ...this.state.tokens }
    const now = Date.now()
    for (const [k, v] of Object.entries(tokens)) {
      if (v.expires <= now) delete tokens[k]
    }
    const accessTokenExpiresAt = now + 60 * 60_000
    const nonce = randomSecret()
    const pair = previous
      ? deriveSuccessor(previous.token, nonce, deviceId)
      : { accessToken: randomSecret(), refreshToken: randomSecret() }
    if (previous) {
      tokens[sha256Hex(previous.token)] = {
        ...previous.record,
        used: true,
        recovery: { nonce, accessExpires: accessTokenExpiresAt },
      }
    }
    tokens[sha256Hex(pair.accessToken)] = { kind: 'access', deviceId, expires: accessTokenExpiresAt, used: false }
    tokens[sha256Hex(pair.refreshToken)] = { kind: 'refresh', deviceId, expires: refreshTokenExpiresAt, used: false }
    const before = this.state.tokens
    this.state.tokens = tokens
    try {
      this.save()
    } catch (err) {
      this.state.tokens = before
      throw err
    }
    return {
      accessToken: pair.accessToken,
      refreshToken: pair.refreshToken,
      accessTokenExpiresAt,
      refreshTokenExpiresAt,
    }
  }

  authenticate(token) {
    const rec = this.state.tokens[sha256Hex(token)]
    if (!rec || rec.kind !== 'access') throw new ApiError('AUTH_INVALID', 401)
    if (rec.expires <= Date.now()) throw new ApiError('TOKEN_EXPIRED', 401)
    return this.get(rec.deviceId)
  }

  refresh(deviceId, token) {
    this.get(deviceId)
    const rec = this.state.tokens[sha256Hex(token)]
    if (!rec || rec.kind !== 'refresh' || rec.deviceId !== deviceId) throw new ApiError('AUTH_INVALID', 401)
    if (rec.expires <= Date.now()) throw new ApiError('TOKEN_EXPIRED', 401)
    if (!rec.used) return this.issue(deviceId, rec.expires, { token, record: rec })
    if (!rec.recovery) throw new ApiError('AUTH_INVALID', 401)
    const pair = deriveSuccessor(token, rec.recovery.nonce, deviceId)
    const next = this.state.tokens[sha256Hex(pair.refreshToken)]
    if (!next || next.kind !== 'refresh' || next.deviceId !== deviceId || next.expires !== rec.expires) {
      throw new ApiError('INTERNAL_ERROR', 503)
    }
    if (next.used) throw new ApiError('AUTH_INVALID', 401)
    return {
      ...pair,
      accessTokenExpiresAt: rec.recovery.accessExpires,
      refreshTokenExpiresAt: next.expires,
    }
  }

  invalidate(deviceId) {
    for (const [k, v] of Object.entries(this.state.tokens)) {
      if (v.deviceId === deviceId) delete this.state.tokens[k]
    }
    this.onInvalidate(deviceId)
    this.save()
  }

  revoke(id) {
    this.get(id).revoked = true
    this.invalidate(id)
  }

  rename(id, name) {
    this.get(id).descriptor.name = String(name).trim().slice(0, 80)
    this.save()
  }

  touch(id, clientVersion, harnessVersion) {
    const d = this.get(id)
    d.lastSeenAt = Date.now()
    if (clientVersion) d.descriptor.clientVersion = String(clientVersion).slice(0, 64)
    if (d.descriptor.role === 'host' && harnessVersion) {
      d.descriptor.harnessVersion = String(harnessVersion).slice(0, 64)
    }
    this.save()
  }
}

// ---------------------------------------------------------------------------
// 4. Minimal RFC 6455 WebSocket Connection Wrapper (Zero External Deps)
// ---------------------------------------------------------------------------
const WS_GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11'

class SimpleWebSocket {
  constructor(socket, head) {
    this.socket = socket
    this.readyState = 1 // OPEN
    this.handlers = { message: [], close: [], error: [] }
    this.buffer = Buffer.alloc(0)
    this.fragments = []
    this.fragmentOpcode = 0

    socket.setNoDelay(true)
    socket.on('data', (chunk) => this._onData(chunk))
    socket.on('error', (err) => this._emit('error', err))
    socket.on('close', () => {
      if (this.readyState !== 3) {
        this.readyState = 3
        this._emit('close', 1006, '')
      }
    })
    if (head && head.length > 0) this._onData(head)
  }

  get bufferedAmount() {
    return this.socket.writableLength || 0
  }

  on(event, fn) {
    if (this.handlers[event]) this.handlers[event].push(fn)
  }

  _emit(event, ...args) {
    for (const fn of this.handlers[event] || []) {
      try {
        fn(...args)
      } catch (err) {
        console.error('[ws handler error]', err)
      }
    }
  }

  _encodeFrame(opcode, payloadBuf) {
    const len = payloadBuf.length
    let header
    if (len < 126) {
      header = Buffer.alloc(2)
      header[0] = 0x80 | opcode
      header[1] = len
    } else if (len < 65536) {
      header = Buffer.alloc(4)
      header[0] = 0x80 | opcode
      header[1] = 126
      header.writeUInt16BE(len, 2)
    } else {
      header = Buffer.alloc(10)
      header[0] = 0x80 | opcode
      header[1] = 127
      header.writeBigUInt64BE(BigInt(len), 2)
    }
    return Buffer.concat([header, payloadBuf])
  }

  send(text) {
    if (this.readyState !== 1) return
    const payload = Buffer.from(text, 'utf8')
    this.socket.write(this._encodeFrame(0x1, payload))
  }

  pong(payload = Buffer.alloc(0)) {
    if (this.readyState !== 1) return
    this.socket.write(this._encodeFrame(0xA, payload))
  }

  close(code = 1000, reason = '') {
    if (this.readyState >= 2) return
    this.readyState = 2
    const reasonBuf = Buffer.from(reason, 'utf8').subarray(0, 123)
    const payload = Buffer.alloc(2 + reasonBuf.length)
    payload.writeUInt16BE(code, 0)
    reasonBuf.copy(payload, 2)
    try {
      this.socket.write(this._encodeFrame(0x8, payload))
    } catch {}
    try {
      this.socket.end()
    } catch {}
  }

  terminate() {
    this.readyState = 3
    try {
      this.socket.destroy()
    } catch {}
  }

  _onData(chunk) {
    this.buffer = this.buffer.length === 0 ? chunk : Buffer.concat([this.buffer, chunk])
    while (this.buffer.length >= 2) {
      const b0 = this.buffer[0]
      const b1 = this.buffer[1]
      const fin = (b0 & 0x80) !== 0
      const opcode = b0 & 0x0f
      const masked = (b1 & 0x80) !== 0
      let payloadLen = b1 & 0x7f
      let offset = 2

      if (payloadLen === 126) {
        if (this.buffer.length < 4) return
        payloadLen = this.buffer.readUInt16BE(2)
        offset = 4
      } else if (payloadLen === 127) {
        if (this.buffer.length < 10) return
        const bigLen = this.buffer.readBigUInt64BE(2)
        if (bigLen > BigInt(MAX_RELAY_FRAME_BYTES + 65536)) {
          this.close(1009, 'FRAME_TOO_LARGE')
          return
        }
        payloadLen = Number(bigLen)
        offset = 10
      }

      if (payloadLen > MAX_RELAY_FRAME_BYTES + 65536) {
        this.close(1009, 'FRAME_TOO_LARGE')
        return
      }

      const maskLen = masked ? 4 : 0
      const totalLen = offset + maskLen + payloadLen
      if (this.buffer.length < totalLen) return

      let payload
      if (masked) {
        const mask = this.buffer.subarray(offset, offset + 4)
        payload = Buffer.allocUnsafe(payloadLen)
        const start = offset + 4
        for (let i = 0; i < payloadLen; i++) {
          payload[i] = this.buffer[start + i] ^ mask[i & 3]
        }
      } else {
        payload = Buffer.from(this.buffer.subarray(offset, offset + payloadLen))
      }
      this.buffer = this.buffer.subarray(totalLen)

      if (opcode === 0x8) {
        // Close frame
        const code = payload.length >= 2 ? payload.readUInt16BE(0) : 1000
        const reason = payload.length > 2 ? payload.subarray(2).toString('utf8') : ''
        this.close(code, reason)
        this.readyState = 3
        this._emit('close', code, reason)
        return
      }
      if (opcode === 0x9) {
        // Ping -> Pong
        this.pong(payload)
        continue
      }
      if (opcode === 0xA) {
        // Pong -> ignore
        continue
      }
      if (opcode === 0x1 || opcode === 0x2) {
        this.fragmentOpcode = opcode
        this.fragments = [payload]
      } else if (opcode === 0x0) {
        this.fragments.push(payload)
      } else {
        this.close(1002, 'INVALID_OPCODE')
        return
      }

      if (fin) {
        const full = this.fragments.length === 1 ? this.fragments[0] : Buffer.concat(this.fragments)
        const isBinary = this.fragmentOpcode === 0x2
        this.fragments = []
        this.fragmentOpcode = 0
        this._emit('message', full, isBinary)
      }
    }
  }
}

// ---------------------------------------------------------------------------
// 5. DSH Remote Control & Relay Gateway
// ---------------------------------------------------------------------------
class RelayGateway {
  constructor(httpServer, store, options = {}) {
    this.store = store
    this.peers = new Map()
    this.links = new Map()
    this.sockets = new Set()
    this.helloTimeoutMs = options.helloTimeoutMs ?? 10_000
    this.heartbeatIntervalMs = options.heartbeatIntervalMs ?? 25_000
    this.heartbeatDisconnectMs = options.heartbeatDisconnectMs ?? 75_000
    this.turnEnabled = Boolean(options.turnEnabled)
    this.closed = false

    this.store.onInvalidate = (id) => this.disconnect(id, 'AUTH_INVALID')

    httpServer.on('upgrade', (req, socket, head) => {
      const path = (req.url || '').split('?')[0]
      if (path !== '/ws/v1/connect') {
        socket.end('HTTP/1.1 404 Not Found\r\nConnection: close\r\n\r\n')
        return
      }
      const key = req.headers['sec-websocket-key']
      if (!key) {
        socket.end('HTTP/1.1 400 Bad Request\r\nConnection: close\r\n\r\n')
        return
      }
      const accept = createHash('sha1').update(key + WS_GUID).digest('base64')
      socket.write(
        'HTTP/1.1 101 Switching Protocols\r\n' +
        'Upgrade: websocket\r\n' +
        'Connection: Upgrade\r\n' +
        `Sec-WebSocket-Accept: ${accept}\r\n\r\n`
      )
      const ws = new SimpleWebSocket(socket, head)
      this.sockets.add(ws)
      this._accept(ws)
    })

    this.heartbeat = setInterval(() => {
      if (this.closed) return
      const now = Date.now()
      for (const peer of this.peers.values()) {
        if (now - peer.lastPong > this.heartbeatDisconnectMs) {
          console.log(`[gateway] heartbeat timeout: ${peer.role} ${peer.id}`)
          this.disconnect(peer.id, 'CONNECTION_FAILED')
          continue
        }
        const nonce = randomUUID()
        peer.pendingNonces.push(nonce)
        if (peer.pendingNonces.length > 3) peer.pendingNonces.shift()
        this.send(peer, createControlFrame('ping', { nonce }))
      }
      for (const link of this.links.values()) {
        if (link.stage !== 'ready' && now - link.created > 30_000) {
          this.dropLink(link, 'CONNECTION_FAILED')
        }
      }
    }, this.heartbeatIntervalMs)
    this.heartbeat.unref()
  }

  send(peer, frame) {
    if (peer.ws.readyState !== 1) return
    if (peer.ws.bufferedAmount > 4 * MAX_RELAY_FRAME_BYTES) {
      this.disconnect(peer.id, 'SLOW_CONSUMER')
      return
    }
    peer.ws.send(JSON.stringify(frame))
  }

  dropLink(link, code) {
    this.links.delete(link.id)
    for (const id of [link.host, link.client]) {
      const p = this.peers.get(id)
      if (p) this.send(p, createControlFrame('error', { code, message: code, connectionId: link.id, retryable: true }))
    }
  }

  disconnect(id, code) {
    const peer = this.peers.get(id)
    this.peers.delete(id)
    for (const link of [...this.links.values()]) {
      if (link.host === id || link.client === id) this.dropLink(link, code)
    }
    if (!peer) return
    console.log(`[gateway] peer disconnected: ${peer.role} ${id} (${code})`)
    peer.ws.close(code === 'CONNECTION_REPLACED' ? 4003 : 4001, code)
  }

  authorizeIce(deviceId, connectionId) {
    const link = this.links.get(connectionId)
    if (!link) return false
    if (link.host !== deviceId && link.client !== deviceId) return false
    if (link.stage === 'pending') return false
    return this.peers.has(link.host) && this.peers.has(link.client)
  }

  _negotiatedCapabilities(offered) {
    const allowed = SUPPORTED_TRANSPORTS.filter((c) => c !== 'transport.turn' || this.turnEnabled)
    const list = Array.isArray(offered) ? offered : []
    return allowed.filter((c) => list.includes(c))
  }

  _accept(ws) {
    let state = 'awaiting_hello'
    let peer

    const deadline = setTimeout(() => {
      if (state !== 'awaiting_hello') return
      state = 'closing'
      ws.send(JSON.stringify(createControlFrame('error', {
        code: 'HELLO_TIMEOUT',
        message: 'Hello handshake timed out.',
        retryable: true,
      })))
      ws.close(4001, 'HELLO_TIMEOUT')
    }, this.helloTimeoutMs)
    deadline.unref()

    ws.on('close', () => {
      clearTimeout(deadline)
      this.sockets.delete(ws)
      state = 'closed'
      if (peer && this.peers.get(peer.id) === peer) {
        this.disconnect(peer.id, 'CONNECTION_FAILED')
      }
    })

    ws.on('message', (raw, isBinary) => {
      if (state !== 'awaiting_hello' && state !== 'authenticated') return
      let frame
      try {
        if (isBinary) throw new ApiError('INVALID_MESSAGE')
        frame = JSON.parse(raw.toString('utf8'))
        if (!frame || frame.v !== PROTOCOL_VERSION || typeof frame.type !== 'string') {
          throw new ApiError('UNSUPPORTED_VERSION')
        }
        if (state === 'awaiting_hello') {
          if (frame.type !== 'hello') throw new ApiError('AUTH_REQUIRED')
          const p = frame.payload || {}
          const device = this.store.authenticate(p.accessToken).descriptor
          if (device.deviceId !== p.deviceId || device.role !== p.role) throw new ApiError('AUTH_INVALID')
          if (!Array.isArray(p.protocols) || !p.protocols.includes(1)) throw new ApiError('UNSUPPORTED_VERSION')
          clearTimeout(deadline)
          state = 'authenticated'
          this.disconnect(device.deviceId, 'CONNECTION_REPLACED')
          const caps = this._negotiatedCapabilities(p.capabilities)
          if (!caps.includes('transport.relay')) caps.push('transport.relay')
          peer = {
            ws,
            id: device.deviceId,
            role: device.role,
            capabilities: caps,
            version: p.clientVersion || device.clientVersion || '0.6.7',
            lastPong: Date.now(),
            pendingNonces: [],
          }
          this.peers.set(peer.id, peer)
          this.store.touch(peer.id, p.clientVersion, p.harnessVersion)
          console.log(`[gateway] ONLINE: ${peer.role} "${device.name}" (${peer.id})`)
          const webrtcEnabled = caps.some((c) => c === 'transport.lan' || c === 'transport.p2p' || c === 'transport.turn')
          this.send(peer, createControlFrame('hello.ack', {
            protocol: 1,
            serverVersion: 'self-hosted-antigravity/1.0.0',
            connectionSessionId: randomUUID(),
            heartbeatIntervalMs: this.heartbeatIntervalMs,
            maxControlFrameBytes: MAX_CONTROL_FRAME_BYTES,
            maxRelayFrameBytes: MAX_RELAY_FRAME_BYTES,
            capabilities: caps,
            webrtcEnabled,
            webrtcFallbackTimeoutMs: webrtcEnabled && !this.turnEnabled ? 3_000 : 12_000,
          }))
          return
        }
        if (frame.type === 'hello') throw new ApiError('INVALID_MESSAGE')
        if (!peer || this.peers.get(peer.id) !== peer) throw new ApiError('AUTH_INVALID')
        this._handleFrame(peer, frame)
      } catch (err) {
        const code = err instanceof ApiError ? err.code : 'INVALID_MESSAGE'
        const connId = frame?.payload?.connectionId
        if (peer && typeof connId === 'string') {
          const link = this.links.get(connId)
          if (link && (link.host === peer.id || link.client === peer.id)) {
            this.dropLink(link, code)
            return
          }
          this.send(peer, createControlFrame('error', { code, message: code, connectionId: connId, retryable: false }))
          return
        }
        state = 'closing'
        clearTimeout(deadline)
        ws.send(JSON.stringify(createControlFrame('error', { code, message: code, retryable: false })))
        if (peer) this.disconnect(peer.id, code)
        else ws.close(4001, code)
      }
    })
  }

  _handleFrame(peer, frame) {
    const p = frame.payload || {}
    if (frame.type === 'ping') {
      this.send(peer, createControlFrame('pong', { nonce: p.nonce }))
      return
    }
    if (frame.type === 'pong') {
      if (typeof p.nonce === 'string') {
        const idx = peer.pendingNonces.indexOf(p.nonce)
        if (idx !== -1) {
          peer.lastPong = Date.now()
          peer.pendingNonces.splice(0, idx + 1)
        }
      }
      return
    }
    if (frame.type === 'connect.request') {
      if (peer.role !== 'client') throw new ApiError('MEMBERSHIP_REQUIRED')
      const host = this.peers.get(p.hostDeviceId)
      if (!host || host.role !== 'host') {
        this.send(peer, createControlFrame('error', { code: 'HOST_OFFLINE', message: 'Host is offline.', retryable: true }))
        return
      }
      this.store.get(host.id)
      const reqTransports = Array.isArray(p.preferredTransports) ? p.preferredTransports : ['relay']
      const preferredTransports = [...new Set(reqTransports)].filter(
        (t) => peer.capabilities.includes(`transport.${t}`) && host.capabilities.includes(`transport.${t}`)
      )
      if (preferredTransports.length === 0) preferredTransports.push('relay')
      for (const old of [...this.links.values()]) {
        if (old.client === peer.id) this.dropLink(old, 'CONNECTION_REPLACED')
      }
      const link = {
        id: randomUUID(),
        host: host.id,
        client: peer.id,
        stage: 'pending',
        created: Date.now(),
        counters: new Map(),
        preferredTransports,
      }
      this.links.set(link.id, link)
      this.send(host, createControlFrame('connect.incoming', {
        connectionId: link.id,
        clientDeviceId: peer.id,
        clientIdentityKey: this.store.get(peer.id).descriptor.identityKey,
        authorization: 'account',
        preferredTransports,
      }))
      return
    }

    const link = typeof p.connectionId === 'string' ? this.links.get(p.connectionId) : undefined
    if (!link || (peer.id !== link.host && peer.id !== link.client)) throw new ApiError('CONNECTION_NOT_FOUND')
    const otherId = peer.id === link.host ? link.client : link.host
    const other = this.peers.get(otherId)
    if (!other) throw new ApiError('CONNECTION_FAILED')

    if (frame.type === 'connect.accepted' || frame.type === 'connect.rejected') {
      if (peer.id !== link.host || link.stage !== 'pending') throw new ApiError('INVALID_MESSAGE')
      if (frame.type === 'connect.rejected') this.links.delete(link.id)
      else link.stage = 'accepted'
      this.send(other, frame)
      return
    }

    if (p.targetDeviceId !== otherId || link.stage === 'pending') throw new ApiError('CONNECTION_NOT_FOUND')

    if (frame.type.startsWith('signal.')) {
      if (link.stage !== 'ready' && link.preferredTransports.some((t) => t !== 'relay')) {
        this.send(other, frame)
      }
      return
    }

    if (frame.type === 'transport.selected') {
      if (peer.id !== link.client) return
      if (TRANSPORT_NAMES.includes(p.transport)) {
        this.send(other, frame)
      }
      return
    }

    if (frame.type === 'secure.handshake') {
      if (p.step === 1 && peer.id === link.client && link.stage === 'accepted') link.stage = 'handshake'
      else if (p.step === 2 && peer.id === link.host && link.stage === 'handshake') link.stage = 'ready'
      else throw new ApiError('INVALID_MESSAGE')
      this.send(other, frame)
      return
    }

    if (frame.type === 'relay') {
      const counter = p.counter
      if (link.stage !== 'ready' || typeof counter !== 'number' || counter <= (link.counters.get(peer.id) ?? -1)) {
        throw new ApiError('INVALID_MESSAGE')
      }
      link.counters.set(peer.id, counter)
      this.send(other, frame)
      return
    }

    throw new ApiError('INVALID_MESSAGE')
  }

  close() {
    if (this.closed) return
    this.closed = true
    clearInterval(this.heartbeat)
    this.peers.clear()
    this.links.clear()
    for (const ws of this.sockets) {
      ws.close(SERVER_SHUTDOWN_CLOSE_CODE, SERVER_SHUTDOWN_CLOSE_REASON)
    }
    this.sockets.clear()
  }
}

// ---------------------------------------------------------------------------
// 6. HTTP Server Factory
// ---------------------------------------------------------------------------
async function readJsonBody(req) {
  const chunks = []
  let len = 0
  for await (const c of req) {
    len += c.length
    if (len > 32768) throw new ApiError('FRAME_TOO_LARGE', 413)
    chunks.push(c)
  }
  try {
    return JSON.parse(Buffer.concat(chunks).toString('utf8'))
  } catch {
    throw new ApiError('INVALID_MESSAGE', 400)
  }
}

function sendJson(res, status, value) {
  res.writeHead(status, { 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store' })
  res.end(JSON.stringify(value))
}

export function createSelfHostedRelayServer(config) {
  const account = String(config.account || '').trim()
  const password = String(config.password || '')
  if (!account || password.length < 12) {
    throw new Error('DSH_SERVER_ACCOUNT and DSH_SERVER_PASSWORD (at least 12 characters) are required.')
  }
  const publicUrl = config.publicUrl || `http://localhost:${config.port || 8080}`
  const dataFile = config.dataFile || join(__dirname, 'data', 'state.json')
  const store = new RelayStore(dataFile, account, password)
  const sessions = new Map()
  const stunUrls = (config.stunUrls || '').split(',').map((s) => s.trim()).filter(Boolean)

  function extractToken(req) {
    const auth = req.headers.authorization
    if (auth) return auth.startsWith('Bearer ') ? auth.slice(7) : ''
    const m = /(?:^|;\s*)dsh_session=([A-Za-z0-9_-]+)/.exec(req.headers.cookie || '')
    return m ? m[1] : ''
  }

  function requireAccountAuth(req) {
    const key = sha256Hex(extractToken(req))
    const exp = sessions.get(key) || 0
    if (exp <= Date.now()) {
      sessions.delete(key)
      throw new ApiError('ACCOUNT_AUTH_REQUIRED', 401)
    }
  }

  function requireDeviceAuth(req) {
    const auth = req.headers.authorization || ''
    if (!auth.startsWith('Bearer ')) throw new ApiError('AUTH_REQUIRED', 401)
    return store.authenticate(auth.slice(7))
  }

  const profile = () => ({ account: store.account, profile: { displayName: store.account }, isAdmin: false })
  const server = createServer({ requestTimeout: 15000, headersTimeout: 10000 }, (req, res) => {
    void route(req, res).catch((err) => {
      if (res.headersSent || res.destroyed) return
      const e = err instanceof ApiError ? err : new ApiError('INTERNAL_ERROR', 500)
      sendJson(res, e.status, {
        error: {
          code: e.code,
          message: e.code,
          requestId: randomUUID(),
          retryable: e.status >= 500,
        },
      })
    })
  })

  const gateway = new RelayGateway(server, store, {
    heartbeatIntervalMs: config.heartbeatIntervalMs,
    heartbeatDisconnectMs: config.heartbeatDisconnectMs,
  })

  function toDescriptor(saved) {
    return {
      ...saved.descriptor,
      membershipId: `account:${sha256Hex(store.account).slice(0, 16)}`,
      online: gateway.peers.has(saved.descriptor.deviceId),
      lastSeenAt: saved.lastSeenAt,
    }
  }

  async function route(req, res) {
    const parsedUrl = new URL(req.url || '/', 'http://localhost')
    const path = parsedUrl.pathname
    const method = req.method

    if (method === 'GET' && (path === '/health' || path === '/healthz' || path === '/ready')) {
      sendJson(res, 200, { status: 'ok', onlinePeers: gateway.peers.size })
      return
    }

    if (method === 'GET' && path === '/') {
      const hosts = store.list().filter((d) => d.descriptor.role === 'host').map(toDescriptor)
      const html = `<!doctype html><html lang="zh-CN"><head><meta charset="utf-8"><title>DSH Self-Hosted Relay</title>
<style>body{font-family:system-ui,sans-serif;max-width:720px;margin:40px auto;padding:0 20px;background:#faf8f5;color:#1e293b}
.card{background:#fff;border:1px solid #e2e8f0;border-radius:12px;padding:20px;margin:16px 0}
.badge{display:inline-block;padding:2px 10px;border-radius:99px;font-size:12px;font-weight:600}
.on{background:#dcfce7;color:#166534}.off{background:#f1f5f9;color:#64748b}</style></head><body>
<h1>DSH Remote 自建中继服务器</h1>
<div class="card"><p><b>状态：</b>运行中 | <b>账号：</b>${store.account} | <b>公网/访问地址：</b>${publicUrl}</p>
<p>在手机 <b>dsh-go</b> 中选择「自建服务器」，填写本服务器地址与邮箱密码登录即可连接。</p></div>
<div class="card"><h3>已注册主机 (${hosts.length})</h3>${
  hosts.length === 0
    ? '<p>暂无主机注册，请在 Antigravity 插件中填写本服务器地址并登录。</p>'
    : hosts.map((h) => `<p><span class="badge ${h.online ? 'on' : 'off'}">${h.online ? '在线' : '离线'}</span> <b>${h.name}</b> (${h.platform}) — <code>${h.deviceId}</code></p>`).join('')
}</div></body></html>`
      res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8' })
      res.end(html)
      return
    }

    if (method === 'POST' && path === '/api/v1/auth/login') {
      const creds = await readJsonBody(req)
      const email = String(creds?.email || '').trim()
      const pass = String(creds?.password || '')
      if (!email || !pass || !constEqual(email, store.account) || !constEqual(pass, password)) {
        throw new ApiError('AUTH_INVALID', 401)
      }
      const value = randomSecret()
      const expiresAt = Date.now() + 8 * 3600_000
      sessions.set(sha256Hex(value), expiresAt)
      res.setHeader('Set-Cookie', `dsh_session=${value}; Path=/; HttpOnly; SameSite=Lax; Max-Age=${8 * 3600}`)
      sendJson(res, 200, { ...profile(), token: value, expiresAt })
      return
    }

    if (method === 'GET' && path === '/api/v1/auth/me') {
      requireAccountAuth(req)
      sendJson(res, 200, profile())
      return
    }

    if (method === 'POST' && path === '/api/v1/auth/logout') {
      sessions.delete(sha256Hex(extractToken(req)))
      res.setHeader('Set-Cookie', 'dsh_session=; Path=/; HttpOnly; Max-Age=0')
      sendJson(res, 200, { status: 'ok' })
      return
    }

    if (method === 'GET' && path === '/api/v1/account/devices') {
      requireAccountAuth(req)
      sendJson(res, 200, { items: store.list().map(toDescriptor), serverUrl: publicUrl, transport: 'webrtc' })
      return
    }

    if (method === 'POST' && (path === '/api/v1/devices/register' || path === '/api/v1/devices/register-owned-role')) {
      const source = path.endsWith('register-owned-role') ? requireDeviceAuth(req) : undefined
      if (!source) requireAccountAuth(req)
      const payload = await readJsonBody(req)
      const device = payload?.device
      if (!device) throw new ApiError('INVALID_MESSAGE', 400)
      if (source && (source.descriptor.deviceId === device.deviceId || source.descriptor.role === device.role)) {
        throw new ApiError('INVALID_MESSAGE', 409)
      }
      sendJson(res, 200, store.register(device))
      return
    }

    if (method === 'POST' && path === '/api/v1/auth/refresh') {
      const data = await readJsonBody(req)
      sendJson(res, 200, store.refresh(String(data?.deviceId || ''), String(data?.refreshToken || '')))
      return
    }

    if (method === 'DELETE' && path === '/api/v1/devices/self') {
      store.revoke(requireDeviceAuth(req).descriptor.deviceId)
      sendJson(res, 200, { status: 'revoked' })
      return
    }

    if (method === 'GET' && path === '/api/v1/me') {
      sendJson(res, 200, toDescriptor(requireDeviceAuth(req)))
      return
    }

    if (method === 'GET' && path === '/api/v1/turn/credentials') {
      const source = requireDeviceAuth(req)
      const connectionId = parsedUrl.searchParams.get('connection_id') || ''
      if (!connectionId || !gateway.authorizeIce(source.descriptor.deviceId, connectionId)) {
        throw new ApiError('CONNECTION_NOT_FOUND', 404)
      }
      sendJson(res, 200, { iceServers: stunUrls.length > 0 ? [{ urls: stunUrls }] : [] })
      return
    }

    if (method === 'GET' && path === '/api/v1/devices') {
      const source = requireDeviceAuth(req)
      if (source.descriptor.role !== 'client') throw new ApiError('MEMBERSHIP_REQUIRED', 403)
      const items = store.list()
        .filter((d) => d.descriptor.role === 'host')
        .map((d) => {
          const { identityKey: _ignored, ...rest } = toDescriptor(d)
          return rest
        })
      sendJson(res, 200, { items, nextCursor: null })
      return
    }

    const renameMatch = /^\/api\/v1\/devices\/([^/]+)\/name$/.exec(path)
    if (method === 'POST' && renameMatch) {
      requireAccountAuth(req)
      const payload = await readJsonBody(req)
      store.rename(decodeURIComponent(renameMatch[1]), payload?.name)
      sendJson(res, 200, toDescriptor(store.get(decodeURIComponent(renameMatch[1]))))
      return
    }

    const deviceMatch = /^\/api\/v1\/devices\/([^/]+)(\/presence)?$/.exec(path)
    if (method === 'GET' && deviceMatch) {
      const source = requireDeviceAuth(req)
      const target = store.get(decodeURIComponent(deviceMatch[1]))
      if (source.descriptor.role === target.descriptor.role) throw new ApiError('MEMBERSHIP_REQUIRED', 403)
      const desc = toDescriptor(target)
      sendJson(
        res,
        200,
        deviceMatch[2] ? { deviceId: desc.deviceId, online: desc.online, lastSeenAt: desc.lastSeenAt } : desc
      )
      return
    }

    throw new ApiError('METHOD_NOT_FOUND', 404)
  }

  return {
    server,
    store,
    gateway,
    close: async () => {
      gateway.close()
      server.closeAllConnections?.()
      await new Promise((resolveClose) => server.close(() => resolveClose()))
    },
  }
}

// ---------------------------------------------------------------------------
// 7. CLI Entry Point
// ---------------------------------------------------------------------------
const isMain = process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)
if (isMain) {
  loadEnvFile(join(__dirname, '.env'))
  const host = process.env.DSH_SERVER_HOST || '0.0.0.0'
  const port = Number(process.env.PORT || process.env.DSH_SERVER_PORT || 8080)
  const account = process.env.DSH_SERVER_ACCOUNT || 'admin@local.dsh'
  const password = process.env.DSH_SERVER_PASSWORD || 'Antigravity2026!'
  const publicUrl = process.env.DSH_SERVER_PUBLIC_URL
    || process.env.RENDER_EXTERNAL_URL
    || (process.env.SPACE_HOST ? `https://${process.env.SPACE_HOST}` : `http://127.0.0.1:${port}`)
  const dataFile = process.env.DSH_SERVER_DATA_FILE
    ? resolve(__dirname, process.env.DSH_SERVER_DATA_FILE)
    : (process.env.SPACE_ID ? '/tmp/dsh-state.json' : join(__dirname, 'data', 'state.json'))

  const instance = createSelfHostedRelayServer({
    account,
    password,
    publicUrl,
    dataFile,
    port,
    stunUrls: process.env.DSH_SERVER_STUN_URLS || '',
  })

  instance.server.listen(port, host, () => {
    console.log('====================================================')
    console.log(' DSH Remote Self-Hosted Relay Server is RUNNING')
    console.log(` Listen  : http://${host}:${port}`)
    console.log(` Account : ${account}`)
    console.log(` Data    : ${dataFile}`)
    console.log('====================================================')
  })

  const shutdown = () => {
    void instance.close().finally(() => process.exit(0))
  }
  process.on('SIGINT', shutdown)
  process.on('SIGTERM', shutdown)
}
