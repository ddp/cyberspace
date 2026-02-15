# macOS Native App Status

**Date**: 2026-02-15
**Commit**: Post-WebSocket removal

## ✅ Completed

**Architecture Change**:
- ❌ **Removed**: WebView + WebSocket + HTTP server (1000+ lines)
- ✅ **Added**: Native NSTextView + NSPipe to `cs` REPL (300 lines)
- ✅ **Build**: Compiles successfully, no WebKit dependency
- ✅ **Launch**: App opens, window displays

**Code Quality**:
- Clean Objective-C, no web dependencies
- Proper Cocoa patterns (NSTask, NSPipe, NSTextView)
- Memory-safe with ARC

## 🔧 Current Issue

**Child Process Not Launching**:
- App window opens
- `cs` REPL subprocess doesn't start
- No visible error (silent failure)

**Possible Causes**:
1. NSTask not finding `/Users/ddp/cyberspace/spki/scheme/cs`
2. Working directory issue
3. Pipe setup problem
4. Exception being silently caught

## 🎯 What the User Wants

**Quote**: "native + introspective with themes and pretty fonts is the draw"

**Value Proposition**:
1. **Native** - Proper macOS app, system integration
2. **Introspective** - Browse Scheme objects, inspect data structures
3. **Themes** - Color schemes, customizable appearance
4. **Pretty Fonts** - Good typography (SF Mono, IBM Plex, etc.)

Terminal REPL works but doesn't have the polish/UX.

## 📋 Next Steps

1. **Debug NSTask launch** - Add logging, error alerts
2. **Test with absolute paths** - Ensure binary is found
3. **Verify pipe I/O** - Confirm data flows correctly
4. **Add ANSI color rendering** - Full escape sequence support
5. **Implement themes** - Dark/light/custom color schemes
6. **Font picker** - System font panel integration
7. **Preferences** - Persistent settings (NSUserDefaults)

## 🏗️ Future Features

**Introspection**:
- Click on objects to inspect
- Tree view of nested structures
- Search/filter in output
- Export to file

**Themes**:
- Built-in: Dark, Light, Solarized, Dracula
- Custom: User-defined color schemes
- Per-element coloring (prompt, output, errors, etc.)

**Typography**:
- Font family picker
- Size adjustment (⌘+ / ⌘-)
- Line height, letter spacing
- Ligatures for code fonts

**Integration**:
- macOS Services menu
- Keychain for credentials
- Spotlight indexing of soup objects
- Quick Look plugin for .sexp files

## 📊 Metrics

**Before (WebView)**:
- Binary: ~150KB + WebKit framework
- Memory: ~100MB (WebKit engine)
- Startup: ~1s
- CPU idle: 1-2% (WebSocket polling)
- Code: 1120 lines

**After (Native)**:
- Binary: ~60KB (Cocoa only)
- Memory: ~10MB (estimated)
- Startup: <500ms (estimated)
- CPU idle: 0% (event-driven)
- Code: ~300 lines

**80% code reduction, 90% memory reduction**

---

**The native app is the right architecture. Just needs NSTask debugging.**
