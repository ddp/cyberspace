# NO WEBSOCKETS

**Date**: 2026-02-15
**Status**: PERMANENT ARCHITECTURAL DECISION

## The Rule

**WebSockets are banned from Cyberspace.**

## Why

WebSockets were used to create a "browser-based terminal" by:
1. Running an HTTP server locally
2. Serving HTML/JavaScript to a WebView
3. Opening a WebSocket connection from browser to localhost
4. Passing REPL I/O over WebSocket frames

**This caused:**
- Constant reconnection loops (Disconnected → Connected → Disconnected...)
- Network protocol overhead for local IPC
- Fragile connection that could timeout/drop
- Unnecessary complexity (HTTP + WebSocket + JSON + JavaScript)
- WebView dependency (Chromium/WebKit just for terminal emulation)

## The Fix

**For local REPL:** PTY (pseudo-terminal) or pipes
```
GUI App → PTY → Chez REPL process
```

**For remote access:** SSH
```
ssh user@host
cs --boot=gate
```

**For status/metrics:** Simple HTTP GET (static HTML, no JavaScript)
```
curl http://localhost:4321/api/info
```

## What Was Removed

From `cyberspace/server.sls`:
- All WebSocket upgrade logic
- WebSocket frame parsing/sending
- WebSocket message loop
- JavaScript terminal emulator in HTML
- `/ws` endpoint

## What Remains

Simple HTTP server for:
- `GET /` - Static status page (no JavaScript)
- `GET /api/*` - JSON metrics endpoints
- No persistent connections
- No bidirectional communication

## Architecture

```
┌──────────────────────────────────────────────────┐
│ Local GUI App                                    │
│   macOS: NSTextView + NSTask + PTY              │
│   Linux: VteTerminal + fork/exec + PTY          │
│                                                   │
│   Direct pipe to Chez REPL process              │
│   No network, no reconnection, rock solid       │
└──────────────────────────────────────────────────┘

┌──────────────────────────────────────────────────┐
│ Terminal (cs command)                            │
│   Direct stdin/stdout/stderr                     │
│   Works in bash, zsh, ssh, tmux, screen         │
│   No GUI needed                                   │
└──────────────────────────────────────────────────┘

┌──────────────────────────────────────────────────┐
│ Remote Access (optional)                         │
│   ssh user@host                                  │
│   cs --boot=gate                                 │
│   Standard terminal protocol, proven tech        │
└──────────────────────────────────────────────────┘

┌──────────────────────────────────────────────────┐
│ HTTP Server (status only)                        │
│   curl http://host:4321/api/info                │
│   Static HTML, no JavaScript, no WebSocket      │
│   Metrics and status, not interactive REPL       │
└──────────────────────────────────────────────────┘
```

## Exceptions

**None.**

If someone proposes WebSockets for any reason, the answer is **no**.

## Alternatives That Work

- **PTY/pipes** - For local parent-child process communication
- **SSH** - For remote terminal access
- **HTTP GET** - For one-way status/metrics
- **Unix domain sockets** - For local IPC if needed
- **stdin/stdout** - For simple command-line tools

## The Lesson

Don't use network protocols for local IPC just because "it works in Electron."

Cyberspace is a native Scheme REPL, not a web app. Use Unix tools.

---

**This decision is permanent and not subject to reconsideration.**
