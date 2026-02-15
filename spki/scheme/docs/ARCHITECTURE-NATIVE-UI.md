# Native UI Architecture - Requirements

**Date**: 2026-02-15
**Status**: Authoritative

## Core Principle

**No WebViews. No embedded HTTP servers for local UI. Fully native on each platform.**

## Rejected Architecture

❌ **Current approach (macOS)**:
```
Cocoa app → WKWebView → http://127.0.0.1:7780 → Chez server → HTML/CSS/JS
```

❌ **Current approach (Linux GTK4)**:
```
GTK4 app → WebKitGTK → http://127.0.0.1:7780 → Chez server → HTML/CSS/JS
```

**Problems**:
- Web-in-a-box masquerading as native
- Unnecessary HTTP server for local-only UI
- xterm.js/web terminal instead of native terminal widget
- Resource overhead (WebKit engine)
- Architectural complexity

## Required Architecture

### macOS

✅ **Native Cocoa terminal**:
```
NSWindow → NSTextView (with terminal emulation)
         → Direct pipe to Chez REPL
         → No HTTP, no WebKit
```

**Options**:
1. Custom NSTextView with ANSI escape handling
2. Use VT100/xterm emulation library (C/Obj-C)
3. NSTask with pipes + attributed string rendering

**Precedent**: Terminal.app, iTerm2 (both native Cocoa, no web tech)

### Linux

✅ **Option A: GTK + VTE** (GNOME-aligned):
```
GTK4 Window → VteTerminal widget
            → Direct pipe to Chez REPL
            → No HTTP, no WebKit
```

**Precedent**: gnome-terminal, Tilix, Guake

✅ **Option B: Pure terminal** (no X11/Wayland):
```
ncurses/termbox → Direct TTY
                → Chez REPL in-process or fork/exec
                → Runs over SSH, in tmux, everywhere
```

**Precedent**: Midnight Commander, vim, emacs -nw

### Windows (Future)

✅ **Native console**:
```
ConPTY (Windows 10+) → Console window
                     → Chez REPL
                     → No HTTP, no Chromium
```

**Precedent**: Windows Terminal, conhost.exe

## HTTP Server Role

The `cyberspace/server.sls` HTTP server is **only** for:

1. **Remote access** - Browser-based access from other machines
2. **Headless servers** - No GUI installed, web UI via nginx reverse proxy
3. **Multi-user** - Serve multiple browser clients
4. **Development** - Quick inspection via `curl http://localhost:7780`

**NOT for local native application UI.**

## Terminal Emulation Requirements

For native apps, implement:

- ✅ ANSI color codes (16 or 256 color)
- ✅ UTF-8 support
- ✅ Scrollback buffer
- ✅ Copy/paste
- ✅ Configurable fonts (monospace)
- ✅ Keyboard shortcuts (platform-specific)

**Do NOT**:
- ❌ Embed a web browser engine
- ❌ Run a local HTTP server
- ❌ Use Electron/CEF/WebView
- ❌ Render terminal via Canvas/WebGL

## Linux: Why No Single "Native" UI?

Linux doesn't have a single platform UI like macOS (Cocoa) or Windows (Win32).

**Options**:
- **GTK** - GNOME ecosystem
- **Qt** - Cross-platform, KDE
- **ncurses** - Terminal-only, universal

**Decision**: Provide **both** GTK (for GNOME users) **and** ncurses (for servers/SSH).

**Rationale**: Cyberspace is a REPL/terminal application. A pure terminal UI is the most "native" Linux approach - works over SSH, in tmux, on headless servers, in Docker containers.

## Implementation Priority

1. **ncurses/terminal** (universal, works everywhere)
2. **macOS Cocoa** (native NSTextView terminal)
3. **Linux GTK+VTE** (for desktop Linux users who want GUI)
4. **Windows ConPTY** (future)

## Deployment Targets

| Platform | UI | Chez Backend | Distribution |
|----------|-----|--------------|--------------|
| macOS | Cocoa terminal | In-app | .app bundle |
| Linux Desktop | GTK+VTE | In-app | .deb/.rpm/Flatpak |
| Linux Server | Terminal-only | Systemd service | Package manager |
| SSH/Remote | Browser (optional) | systemd + nginx | Remote access |

## Code Location

- `darwin/application/` - macOS Cocoa native terminal
- `linux/gtk4/application/` - GTK4 + VTE widget (rewrite needed)
- `linux/minimal/` - ncurses/terminal-only
- `chez/cyberspace/server.sls` - HTTP server (remote access only)

## Migration Path

**Current state**: WebView apps exist but are rejected.

**Action items**:
1. Archive WebView implementations as `darwin/application-webview-DEPRECATED/`
2. Implement native terminal for macOS (NSTextView or VT100 library)
3. Implement ncurses version (highest priority - works everywhere)
4. Rewrite GTK version to use VteTerminal instead of WebKitGTK
5. Update build scripts and CLAUDE.md

---

**Authority**: This document supersedes any WebView-based designs.
**Rationale**: Cyberspace is a native Scheme REPL, not a web app. Native terminals are simpler, faster, and more honest.
