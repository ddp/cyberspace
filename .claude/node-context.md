# Node Context

Last updated: 2026-01-28 08:30 PST by Claude on fluffy

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

## Current State

- REPL: v0.4.0, 44 modules, ~71K LOC
- Lineage: Custom fork with UTF-8 display width, first-char injection, command completion
- Modes: novice (%) and lambda (λ) working, both in whitelist
- Completion: Wired via `enable-command-completion`, paren-wrap toggles per mode

## In Progress

- Nothing active - was testing/fixing mode switching

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
