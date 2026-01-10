# RFC-051: The Normie Interface

**Status:** Informational
**Date:** January 2026
**Author:** Derrell Piper <ddp@eludom.net>

---

## Abstract

Cyberspace must be approachable by normal people. The terminal is for operators. This RFC specifies a friendly interface layer for everyone else.

---

## 1. The Problem

A normie asked: "Why would I want to use this? I have Tahoe 26.2. They have recipes and cat pictures."

Valid question. The answer must be compelling without mentioning:
- Ed25519
- SPKI certificates
- Hash chains
- Merkle trees
- S-expressions

---

## 2. What Normies Want

```
What they have now:          What they actually want:
────────────────────         ────────────────────────
iCloud                       My stuff, always there
Photos app                   My pictures, forever
Notes                        My recipes, shareable
Messages                     Talk to people I trust
```

They don't want a distributed cryptographic vault. They want:

1. **My stuff is mine** - Not rented from a corporation
2. **It survives** - No company shutdown deletes my photos
3. **I control sharing** - Family, not platforms
4. **Privacy** - My recipes aren't AI training data
5. **Legacy** - Grandkids can inherit the vault
6. **No ads** - I'm not the product

---

## 3. The Value Proposition

```
┌─────────────────────────────────────────────────────────────────┐
│                                                                 │
│  A family vault, not a rental locker.                          │
│                                                                 │
│  Your photos. Your recipes. Your letters.                      │
│  Shared with who you choose.                                   │
│  Kept forever. Passed down.                                    │
│                                                                 │
│  No company in the middle.                                     │
│  No terms of service.                                          │
│  No sudden shutdowns.                                          │
│                                                                 │
│  Just you and the people you trust.                            │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## 4. Two Doors

```
                    CYBERSPACE
                        │
           ┌────────────┴────────────┐
           │                         │
      ┌────▼────┐              ┌─────▼─────┐
      │ Terminal │              │  Friendly  │
      │  (cs)    │              │    Door    │
      └────┬────┘              └─────┬─────┘
           │                         │
      Operators                   Normies
      Hackers                     Family
      Admins                      Everyone
```

### 4.1 The Terminal (Operators)

```scheme
: (seal-commit "vacation photos")
: (enroll-request 'mom)
: (federation?)
```

Full power. Full complexity. For those who want it.

### 4.2 The Friendly Door (Normies)

```
┌─────────────────────────────────────────┐
│  Your Vault                    [+ Add]  │
├─────────────────────────────────────────┤
│  📷 Photos         1,234 items          │
│  📝 Recipes          47 items           │
│  📁 Documents       156 items           │
├─────────────────────────────────────────┤
│  Shared with: Mom, Dad, Sister          │
│  [Invite someone]                       │
└─────────────────────────────────────────┘
```

Drag and drop. Click to share. No parens.

---

## 5. Interface Mapping

| Normie Action | What Happens |
|---------------|--------------|
| Drag photo to vault | `(seal-commit "photo.jpg")` |
| Click "Invite Mom" | `(enroll-request 'mom)` |
| View shared items | `(soup 'shared)` |
| Check who's online | `(federation?)` |
| See vault contents | `(vault?)` |

The friendly door calls the same functions. Just no typing.

---

## 6. Onboarding

### 6.1 Terminal Onboarding

```
You are unaffiliated, in the wilderness.

: (self?)
You have no identity yet.
  Use (enroll-request 'your-name) to join a confederation.
```

### 6.2 Friendly Onboarding

```
┌─────────────────────────────────────────┐
│                                         │
│  Welcome to your vault.                 │
│                                         │
│  What's your name?                      │
│  [_______________]                      │
│                                         │
│  [Create my vault]                      │
│                                         │
│  ─────────────────────────────────────  │
│  Already have a vault?                  │
│  [Join family vault]                    │
│                                         │
└─────────────────────────────────────────┘
```

Same operations. Different presentation.

---

## 7. Implementation Notes

The friendly door could be:

1. **Native app** - macOS, iOS, Android, Windows
2. **Web interface** - Local server, browser UI
3. **Electron** - Cross-platform (if we must)
4. **Terminal TUI** - Curses/ncurses for text lovers

All doors lead to the same vault. All use the same Scheme underneath.

---

## 8. Principles

1. **Never dumb down the core** - Scheme stays Scheme
2. **Add layers, don't subtract** - Friendly is additional, not replacement
3. **Same operations** - Both doors do the same things
4. **Gradual revelation** - Normies can discover the terminal if curious
5. **Family friendly** - Grandma can use it

---

## 9. The Test

If a normie can:
- Create a vault in 30 seconds
- Add a photo in 5 seconds
- Invite family in 1 minute
- Understand what they have

Then we've succeeded.

---

## 10. References

1. RFC-002 - Architecture ("English on top, Scheme underneath")
2. RFC-050 - The Wilderness (onboarding state)

---

## Changelog

- **2026-01-10** - Initial specification

---

*The power is there. The door just needs to be wider.*
