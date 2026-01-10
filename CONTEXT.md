# Cyberspace - Context & Philosophy

**"Rough consensus, cryptography, trusted systems and running code."**

## Prime Directive: Language & TCB Separation

**If it's in the TCB, it's in OCaml. Otherwise it's in Chicken Scheme.**

```
┌─────────────────────────────────────┐
│   Chicken Scheme (Everything)      │
│   - Policy, tools, network, UI     │
│   - All user-facing code           │
│   - Human-readable s-expressions   │
└──────────────┬──────────────────────┘
               │ FFI (minimal boundary)
               ▼
┌─────────────────────────────────────┐
│   OCaml TCB (Crypto Only)          │
│   - Signature verify               │
│   - Chain validation               │
│   - libsodium bindings             │
│   - Coq-provable core              │
└─────────────────────────────────────┘
```

**No Common Lisp.** All non-TCB code in Chicken Scheme.

**TCB = Trusted Computing Base:**
- Minimal (1-2K lines of OCaml)
- Verified (Coq proofs)
- Frozen (rarely changes)
- Only crypto operations that MUST be correct

**Non-TCB = Everything Else:**
- Chicken Scheme exclusively
- Policy evaluation, SDSI names, discovery, logging
- CLI tools, network protocols, distributed agents
- Human-readable, auditable, evolvable

## The World

This is **ddp's world**:
- `~/cyberspace` - The Library of Cyberspace
- `~/.emacs` - 803 lines of crafted Elisp
- `~/.zshrc` - Shell translated from tcsh (old-school Unix)

## Who

**ddp@electric-loft.org**
- Decades of Unix/Lisp/functional programming experience
- DNS administrator (servfail/ns1.adelman.com)
- Network operator (fluffy.eludom.net, www.yoyodyne.com)
- Cypherpunk philosophy
- macOS (Apple Silicon)

## Philosophy

**Not corporate:**
- "guards" not "middleware"
- Whimsical terminology for the realm
- Minimal, elegant tools
- No theorizing without running code

**Foundational research → running code:**
- Lampson (capabilities, protection)
- Lamport (time, signatures, OTP, Paxos)
- Merkle (authenticated data structures)
- Bernstein (ChaCha20, Poly1305, curve25519)

**Tools:**
- **Chicken Scheme** - All non-TCB code (policy, tools, network, UI)
- **OCaml** - TCB only (crypto core, verified with Coq)
- **libsodium** - Crypto primitives (via OCaml FFI)
- Emacs with claude-code.el + Monet IDE
- Git for everything
- opam/tuareg/merlin for OCaml development

## The Library (~/cyberspace)

**421 papers across 16 categories:**
- Cryptographers (48 papers) - Lamport, Merkle, Bernstein, Chaum, etc.
- Type Theory/FP/PLT (40 papers)
- Verified Systems (26 papers)
- Lamport Papers (15 papers)
- DEC VAXcluster, DSSA/NCSC, Infosec, Cryptology, etc.

**9 Working Implementations:**
1. `lamport-otp/` - Hash-chain authentication (Lamport 1981)
2. `merkle-tree/` - Authenticated data structures (Merkle 1979)
3. `capabilities/` - Unforgeable tokens (Lampson 1971, 1992)
4. `chacha20/` - ARX stream cipher (Bernstein 2008, RFC 7539)
5. `poly1305/` - Polynomial MAC (Bernstein 2005) [educational]
6. `lamport-signatures/` - Post-quantum signatures (Lamport 1979) [WIP]
7. `spki/` - SPKI/SDSI in OCaml (Lampson, Rivest, et al.)
8. `api/` - HTTP API server (Chicken Scheme)
9. `librarian/` - Distributed agent architecture

**All in Chicken Scheme** (except SPKI which is OCaml)

## Key Aliases & Workflows

```bash
# Main workflow
cyberspace='cd ~/cyberspace && claude -c'

# Scheme
scheme='rlwrap csi'          # Chicken Scheme
chicken='rlwrap csi'
chibi='rlwrap chibi-scheme'
chez='rlwrap chez'
guile='rlwrap guile'

# Common Lisp (architecture-aware)
lisp='rlwrap sbcl --noinform'  # ARM64
lisp='rlwrap ccl'              # x86_64

# Claude
cc='claude --continue'
cr='claude --resume'

# Navigation
..='cd ..'
...='cd ../..'
....='cd ../../..'

# Utilities
please='sudo'
epoch='date +%s'
aliases='alias | sort'
```

## Emacs Configuration Highlights

**Core bindings:**
- `C-c c` - Claude Code transient menu
- `C-c e` - Open ~/.emacs
- `C-c z` - Open ~/.zshrc
- `C-c d` - ddp personal keymap

**ddp keymap (`C-c d`):**
- `n` - Connect to norns (192.168.0.161)
- `o` - Become other (fluffy.eludom.net)
- `s`, `,` - Become servfail
- `.` - Become nameserver (servfail→ns1)
- `y` - Become yoyodyne
- `C-l` - Run Common Lisp (SLY)
- `C-m` - Run OCaml (utop)
- `(` - Run Scheme

**Features:**
- IBM Plex Mono 140pt font
- claude-code.el with Monet IDE integration
- eat terminal backend (avoids vterm bounce)
- TRAMP multi-hop: `/ssh:servfail.adelman.com|ssh:ns1.adelman.com:/path`
- Lambda→λ prettification in Scheme
- Paredit for structural editing
- SLY for Common Lisp
- Tuareg + Merlin for OCaml
- ibuffer with "Seen" column (last viewed timestamp)

## Network Topology

**Local:**
- norns: 192.168.0.161 (we@norns, Lua scripting)
- Local network: 192.168.0.0/24

**Remote:**
- fluffy.eludom.net (primary server)
- servfail.adelman.com (DNS bastion)
- ns1.adelman.com (authoritative nameserver, via servfail)
- www.yoyodyne.com (web server)

**SSH trampolining:**
```
laptop → servfail.adelman.com → ns1.adelman.com → /usr/local/etc/nsd/master/
```

## Deferred Computation Philosophy

**Lazy by default. Force when ready.**

The cyberspace-repl implements deferred computation at multiple levels:

**Lazy Compilation** (content-addressed):
```scheme
(define-lazy name source-hash)  ; register, don't compile
(force-compile name)            ; compile now
(name args...)                  ; auto-compile on first call
```

**Lazy Clustering** (RFC-016):
```scheme
(lazy-join peer uri: u key: k)  ; register peer, no sync yet
(lazy-sync peer)                ; sync when ready
```

**Durability Model**:
```scheme
(ephemeral thing)   ; no promise of persistence
(persist thing)     ; vault-bound, durable
```

The pattern: wrap computation in a thunk, register with content hash,
defer work until needed, cache the result. Classic Scheme philosophy
applied to distributed systems - things exist without promise until
you choose to materialize them.

## Implementation Patterns

**Every implementation follows:**
1. **Research paper** as foundation (cite authors, year, paper title)
2. **Working Chicken Scheme code** with:
   - CLI interface
   - Multiple demos
   - OpenSSL integration where needed
   - Comprehensive comments
3. **README.md** explaining:
   - Conceptual overview
   - How it works
   - Connection to research
   - Real-world applications
   - Security properties
4. **Git commits** with:
   - Clear commit messages
   - "🤖 Generated with Claude Code"
   - "Co-Authored-By: Claude Sonnet 4.5"

**Code style:**
- Functional, minimal mutation
- Clear variable names
- Abundant comments
- Educational focus (not production-hardened)
- Demonstrate concepts from papers

## Current Projects

**Completed:**
- Lamport OTP (hash chains)
- Merkle Trees (inclusion proofs)
- Capabilities (HMAC-signed tokens)
- ChaCha20 (stream cipher, RFC test vectors passing)
- Poly1305 (educational, simplified)
- API server (core framework, library search working)

**In Progress:**
- Lamport Signatures (implementation done, README pending)
- API crypto endpoints (scaffolded, needs integration)

**Planned:**
- Lamport Logical Clocks (distributed time)
- Byzantine Paxos (consensus)
- More cryptographic primitives
- Federation for distributed agents

## Git Workflow

```bash
# Standard commit format
git add <files>
git commit -m "Title

Description of changes and what they demonstrate.

🤖 Generated with Claude Code (https://claude.com/claude-code)

Co-Authored-By: Claude Sonnet 4.5 <noreply@anthropic.com>"

git push origin main
```

## Interaction Style

**What Claude should do:**
- Build working implementations in Chicken Scheme
- Create comprehensive READMEs
- Commit with proper messages
- Use whimsical terminology (guards, not middleware)
- Connect everything back to foundational research
- No corporate speak
- No emoji unless explicitly requested
- Research → Practice → Running Code

**What Claude should NOT do:**
- Theorize without implementing
- Create placeholder code
- Use corporate terminology
- Add emoji by default
- Make assumptions - read files first

## Subscription

**Claude.app Max:**
- Full model access (Opus 4.5, Sonnet 4.5, Haiku)
- Extended context (200k tokens)
- Claude Code CLI
- Priority access

**Permission mode:** acceptEdits (fast workflow for trusted code)

## Remember

This is not a corporate project. This is a personal library of implementations demonstrating foundational cryptographic and distributed systems research. Every line of code should demonstrate a principle. Every implementation should run. Every commit should advance the state of "rough consensus, cryptography, trusted systems and **running code**."

---

**Last Updated:** 2026-01-05

**Current Model:** claude-sonnet-4-5-20250929

**Status:** Building the Library of Cyberspace, one implementation at a time.
