# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when
working with code in this repository.

## Repository Overview

This is a personal dotfiles repository containing Emacs and zsh shell
configurations for macOS. The files in this repository are designed to
be symlinked from the home directory:
- `.emacs` → `~/.emacs`
- `.zshrc` → `~/.zshrc`

## File Structure

### .emacs (24KB, ~700 lines)

Comprehensive Emacs configuration targeting macOS (NS build) with:
- Custom personal keymap (`C-c d` prefix for ddp-specific commands)
- Lisp development: SLY integration with SBCL at `~/bin/sbcl/bin/sbcl`
- OCaml development: tuareg-mode, merlin, company-mode with opam integration
- Scheme development: paredit-mode, pretty lambda (λ), multiple implementations (chibi, chez, guile)
- Lua development: lua-mode for norns script development
- TRAMP configuration for multi-hop SSH editing (servfail→ns1, norns, yoyodyne)
- Custom ibuffer "Seen" column tracking buffer last-viewed timestamps
- Package management via MELPA, MELPA-stable, GNU ELPA

Key paths referenced:
- `~/src/.emacs.d` - Emacs packages and load-path root
- `~/src/lisp` - Common Lisp working directory
- `~/src/scm` - Scheme working directory
- `~/src/ocaml` - OCaml working directory
- `~/bin/sbcl` - SBCL installation
- `~/.saves/` - Backup file directory

### .zshrc (8KB, ~250 lines)

Zsh configuration translated from tcsh with:
- Large history (50K lines) with sharing across sessions
- Homebrew detection for both Apple Silicon (`/opt/homebrew`) and Intel (`/usr/local`)
- Emacsclient wrappers (`ec`, `ect`, `ecg`) connecting to server named "ns"
- SSH host completion from `~/.ssh/known_hosts`
- Extensive alias collection (ls variants, rlwrap for REPLs, development tools)
- OCaml/opam initialization
- SBCL path configuration
- Platform-specific SSH agent handling (macOS Keychain vs Linux ssh-agent)

## Key Dependencies

External tools expected to be available:
- **Emacs.app** at `/Applications/Emacs.app` (macOS GUI version)
- **SBCL** at `~/bin/sbcl/bin/sbcl` with `SBCL_HOME=~/bin/sbcl/lib/sbcl`
- **opam** (OCaml package manager) - auto-detected via `opam var share`
- **Homebrew** - architecture-detected (`/opt/homebrew` or `/usr/local`)
- **rlwrap** - used for REPL readline support (sbcl, chibi, chez, csi, guile)
- **utop** - OCaml REPL (used in shell mode, not integrated with tuareg)

Emacs packages (via package manager):
- `sly` - Superior Lisp Interaction for Common Lisp
- `paredit` - structured editing for S-expressions
- `tuareg` - OCaml major mode
- `merlin` - OCaml type information and completion
- `company` - completion framework
- `lua-mode` - Lua editing
- `exec-path-from-shell` - inherit macOS environment in GUI Emacs

## Important Configuration Details

### Emacs Customizations

- **Server name**: "ns" (NeXTStep) - emacsclient must use `-s ns`
- **Lexical binding**: enabled in .emacs
- **Custom file**: `~/src/.emacs.d/custom.el` (auto-generated)
- **No tabs**: `indent-tabs-mode nil` globally
- **Fill column**: 72 for text/comments
- **Debug loading**: Set `ddp-debug-loading` to `t` to trace require/load timing

### Custom Functions Worth Noting

- `ddp-become-nameserver`: Multi-hop TRAMP to servfail→ns1
- `ddp-become-servfail`: Direct TRAMP to servfail
- `ddp-become-yoyodyne`: TRAMP to www.yoyodyne.com
- `ddp-become-other`: Toggle local/remote on fluffy.eludom.net
- `ddp-norns-connect`: SSH to norns at 192.168.0.161
- `ddp-copy-char-above` / `ddp-copy-to-eol-above`: Copy from line above (C-c <up> with repeat-mode)
- `ddp-run-lisp`: cd to ~/src/lisp and start SLY
- `ddp-run-scheme`: cd to ~/src/scm
- `ddp-run-ocaml`: Start utop in ~/src/ocaml

### TRAMP Multi-hop Configuration

The `.emacs` configures TRAMP proxies for accessing hosts behind a bastion:

```elisp
;; Access ns1.adelman.com via servfail.adelman.com
(add-to-list 'tramp-default-proxies-alist
             '("\\`ns1\\.adelman\\.com\\'" nil
               "/ssh:servfail.adelman.com|ssh:%h:"))
```

### Key Bindings Changed from Defaults

- `C-j`: `backward-kill-word` (not newline-and-indent)
- `C-r`: `query-replace` (not isearch-backward)
- `C-s`: `isearch-forward-regexp` (not isearch-forward)
- `C-c e`: Open ~/.emacs
- `C-c z`: Open ~/.zshrc
- `C-c d`: Prefix for personal keymap (see ddp-map)
- `<f1>`/`<f2>`: Scroll other window
- `<f3>`: `delete-other-windows`
- `<f4>`: `blank-mode` (show whitespace)
- `<f8>`: Call last keyboard macro

## Making Changes

When editing these configuration files:

1. **Test in a new Emacs instance** before committing changes to `.emacs`
2. **Use `source ~/.zshrc`** to test zsh changes in current shell
3. **Preserve the symlink structure** - edit in `~/cyberspace/`, changes reflect to `~`
4. **Check platform assumptions** - configurations assume macOS (darwin)
5. **Respect existing code style**:
   - Emacs: 4-space indentation, no tabs, 72-column fill for comments
   - Use `try-require` for optional Emacs packages to avoid load failures
   - Use `with-eval-after-load` for deferred configuration

## Testing Emacs Configuration

Load .emacs with debug mode enabled:

```bash
/Applications/Emacs.app/Contents/MacOS/Emacs -nw -Q -l ~/.emacs --eval '(setq ddp-debug-loading t)'
```

Check for errors in *Messages* buffer or warnings during startup.

## Deployment

To deploy these dotfiles on a new system:

```bash
cd ~
git clone <repo-url> cyberspace
ln -s ~/cyberspace/.emacs ~/.emacs
ln -s ~/cyberspace/.zshrc ~/.zshrc
```

Then install dependencies:
- Homebrew (if macOS)
- SBCL to `~/bin/sbcl`
- opam and OCaml tools
- Required Emacs packages via `M-x package-list-packages`

## Library Index Management

The `~/cyberspace/library/` directory contains 312+ research PDFs organized by topic (Cryptology, Type Theory, infosec, etc.).

**Permuted Index**: `library/index.html`
- LaTeX-style KWIC (KeyWord In Context) permuted index
- Every significant word indexed with clickable links
- Deduplicated, hierarchical (letter → keyword → documents)
- Regenerate after adding new documents: `~/cyberspace/bin/generate-library-index`

**When to Regenerate**:
- After adding/removing PDFs from library
- When directory structure changes
- When updating DESIGN-SPECIFICATIONS.md or other indexed docs
- Commit both the script and generated index.html to version control

The index integrates with:
- `PERMUTED-INDEX.md` - Main document collection index
- `DESIGN-SPECIFICATIONS.html` - Cyberspace design specifications
- Published at: https://www.yoyodyne.com/ (via `~/bin/publish`)
