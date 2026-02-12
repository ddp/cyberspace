# Node Context

Last updated: 2026-02-12 by Claude on fluffy

## Session History

### 2026-01-27 on starlight (evening)
- Started with reflection/query work across soup, vault, audit, wormhole
- Added `session-stats`, `session-stats-reset!` to os.scm
- Added `wormhole-query`, `wormhole-find`, `wormhole-all-audit` to wormhole.scm
- Added `global-search` and `dashboard` to vault.scm
- Hit massive build regression - dependency ordering was wrong in build.scm
- Fixed: os moved to Level 0, fips/wordlist after crypto-ffi, audit before vault
- EDT module was missing - created stub, then restored full implementation from git
- lineage cursor was off-by-one with λ prompt (UTF-8 display width issue)
- Fixed lineage-src.c: added `utf8_display_width()`, `pwidth` field, `linenoiseWithFirstChar()`
- Fixed box drawing: Chicken's `#\╭` char literals corrupt multi-byte UTF-8, use `"╭"` strings
- User's kitty config: enabled `copy_on_select clipboard`, `cursor_shape block`, `shell_integration no-cursor`
- **Resident editors added** (residents/ directory):
  - `pencil.scm` - Electric Pencil (1976) tribute, WASDZX diamond movement, gap buffer
  - `teco.scm` - Dan Murphy's TECO (1962) tribute, every character is a command
  - `schemacs.scm` - Emacs-style editor in Scheme
  - Loaded once into REPL, always ready (like LSE/VAX Emacs on VMS)

### 2026-01-28 on fluffy (morning)
- Synced from starlight, rebuilt lineage and repl
- lineage-with-first-char wasn't found - had to install lineage to system chicken path
- Fixed `lambda-mode` not in novice-command whitelist
- Added `schemer` alias then removed it (user preference: keep `lambda`/`lambda-mode`, no `schemer`)
- Renamed memo-0060 from collaborative-design to dissertation-notes (user's, don't touch)
- Created this node-context.md for cross-node continuity

### 2026-02 Chez Scheme Port (fluffy + starlight)
- Library hardening: replaced placeholders (AEAD, validity-expired?, HTTP publication),
  added epidemic gossip multi-peer broadcast, query cursors (Memo-027 Phase 1),
  tests for auto-enroll, capability, security
- **Chez port completed across both nodes:**
  - fluffy: sexp, crypto-ffi, bloom, cert, pq-crypto, wordlist, script, merkle,
    security, catalog, keyring, audit, vault (2 phases), gossip, seal CLI,
    query, display, http, enroll, forum, lazy-chunks, piece-table, portal, rope,
    os, objc, tcp, capability, filetype, fips, test framework, compatibility shims
  - starlight: edt, tty-ffi, smelter, forge, info, metadata-ffi, osc, rnbo,
    mdns, text, fuse-ffi, wormhole, inspector, auto-enroll, ui.
    Plus 4 C bridges (tty, metadata, osc, fuse). R6RS import fixes in filetype, fips.
- 45 library modules, 6 compatibility shims, 8 C/ObjC bridges, 17 test files
- Tagged `chez-port-complete`
- Memo-0039 paren balance fix (line 25 closed memo early; lines 112/120 imbalanced
  in Security Considerations). Regenerated and published to Yoyodyne.
- Added Duan et al. "Breaking the Sorting Barrier" (STOC 2025) to research library

## Current State

- REPL: v0.4.0, 44 modules, ~71K LOC (Chicken)
- Chez port: 45 modules, 21K LOC, 42/58 Chicken modules ported (72%)
  - All library-layer code ported; application shell (REPL, CLI tools) remains
- Lineage: Custom fork with UTF-8 display width, first-char injection, command completion
- Modes: novice (%) and lambda (λ) working, both in whitelist
- 60 memos published to Yoyodyne

## Remaining Chez Work

Application layer (depends on all library modules being complete - they are):
- `repl.scm` - The main REPL (4800+ lines, last to port)
- `cyberspace.scm`, `server.scm`, `seal.scm` - Application entry points
- `spki-cert.scm`, `spki-keygen.scm`, `spki-show.scm`, `spki-verify.scm` - CLI tools

Development utilities (low priority):
- `deploy.scm`, `refresh-library.scm`, `refresh-repl.scm`
- `sanity.scm`, `scrutinize.scm`, `scrutinizer.scm`
- `demo-cyberspace.scm`, `mpe.scm`

## Reserved

- Memo-0060: User's dissertation notes - DO NOT EDIT

## Resume Protocol

On session start or after sync, run:
```
git log --oneline -10
git diff --stat HEAD~5
```
Then read any unfamiliar changed files before proceeding.

## Design Decisions

- Prompt uses λ (2 bytes UTF-8, 1 display column) - required lineage pwidth vs plen separation
- REPL intercepts first char for `.`/`?` shortcuts, passes ESC to lineage-with-first-char
- Dashboard/session-stats/global-search explicitly dispatched in REPL to bypass eval's interaction-environment
- No `schemer` command - use `lambda` or `lambda-mode` only
- lineage.so must be installed to system chicken path, not just local eggs/
- Chez binary: `/opt/homebrew/bin/chez` on macOS arm64
- R6RS eval not in `(rnrs)` composite — import from `(chezscheme)` directly
- `session-stat!` pattern for os.sls (R6RS forbids exporting assigned variables)
- Signal handlers are no-ops in Chez (only SIGINT via keyboard-interrupt-handler)
- date(1) shell replaces Chicken's seconds->utc-time for time formatting
