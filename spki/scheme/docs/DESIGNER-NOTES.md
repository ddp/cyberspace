# Cyberspace Designer Notes

## 2026-01-11: REPL UX Principles

### Output Philosophy

- **Silence is default** - Success prints nothing. Failure is an error.
- **No developer notes** - If it's not for the user, it doesn't print. No leaking implementation details.
- **Verbose is opt-in** - `--verbose` for play-by-play, otherwise quiet.
- **Consequential operations may announce** - Enrollment, federation changes, realm joins. But even these should maybe require `--verbose` because they're supposed to work.

### Async Model

- Prompts return frequently, don't block on long operations.
- Background work runs async, notify on completion.
- Notifications are optional - check when you want, never modal, never blocking.
- Your response is never required.

### Introspection by Semantic Type

- Not a generic notification queue.
- Organized by type of operation: enrollments, syncs, votes, federation requests.
- Each reflected where it makes sense in the REPL.
- Introspect by what it *is*, not dig through a queue.

### Governance

- Passive consent: silence is assent to federation consensus.
- If you don't vote, you live with the federation's decision.
- Fork your own security policy in your realm if you disagree.

### VMS Lessons

- $FAO-style formatted output for the TCB - clean ASCII.
- No calling the runtime from the TCB.
- The audit and protected subsystems live in their own UI layer.

## 2026-01-11: Bootstrap Display

Enhanced REPL startup to show:
- Host name, platform stamp (Darwin-arm64)
- Hardware summary (cores, RAM, chip)
- IPv4 and IPv6 addresses
- Vault/enrollment status

Fixed `plural` function for irregular plurals (identity -> identities).
Added IPv6 support to `introspect-network`.
