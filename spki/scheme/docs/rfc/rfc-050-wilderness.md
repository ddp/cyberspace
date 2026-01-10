# RFC-050: The Wilderness

**Status:** Informational
**Date:** January 2026
**Author:** Derrell Piper <ddp@eludom.net>

---

## Abstract

This RFC defines the Wilderness - the interstitial space between realms in Cyberspace. It establishes the cosmology of realms, wormholes, and affiliation.

---

## 1. The Wilderness

The Wilderness is the space between all realms. It is not empty - it is the medium through which all connections pass.

```
┌─────────────────────────────────────────────────────────────────┐
│                                                                 │
│                      THE WILDERNESS                             │
│                                                                 │
│      ┌─────────┐              ┌─────────┐                      │
│      │ Realm A │──wormhole───►│ Realm B │                      │
│      └─────────┘              └─────────┘                      │
│                                                                 │
│                    ┌─────────┐                                  │
│                    │ Realm C │                                  │
│                    └─────────┘                                  │
│                         ↑                                       │
│                    (you are here)                               │
│                    (unaffiliated)                               │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## 2. States of Being

### 2.1 Unaffiliated

When you first enter Cyberspace, you are unaffiliated. You exist in the Wilderness with no realm to call home.

```
You are unaffiliated, in the wilderness.
```

This is the starting state. You have not:
- Instantiated your own realm
- Joined a confederation
- Established any identity

### 2.2 Realm Instantiation

To leave the Wilderness, you must instantiate a realm:

```scheme
(create-realm 'myname)    ; create your own realm
;; or
(enroll-request 'myname)  ; join an existing confederation
```

Once affiliated, you have a home:

```
You entered the yoyodyne realm 5 minutes ago.
```

### 2.3 Wormhole Transit

Wormholes punch through the Wilderness to connect realms. When traversing a wormhole, you pass through the Wilderness - the same Wilderness where the unaffiliated wait.

```
realm A ──► [wilderness] ──► realm B
                 ↑
            wormhole transit
```

---

## 3. Properties of the Wilderness

### 3.1 Universality

There is one Wilderness. All realms exist as islands within it. All wormholes traverse it.

### 3.2 Neutrality

The Wilderness belongs to no one. It has no authority, no governance, no federation. It simply is.

### 3.3 Connectivity

The Wilderness enables connection. Without it, realms would be isolated. Wormholes work because they have something to traverse.

---

## 4. The Wilderness of Mirrors

The name evokes the intelligence world's "wilderness of mirrors" - a space of uncertainty, reflection, and misdirection. In Cyberspace:

- Trust is not given, it is established
- Identity is not assumed, it is proven
- Affiliation is not automatic, it is earned

The Wilderness is honest about this. You are alone until you prove otherwise.

---

## 5. User Interface

### 5.1 Status Line

```
wilderness │ just now │ quiet
```

When affiliated:

```
yoyodyne │ 5 minutes │ replicating
```

### 5.2 Introspection

```scheme
(self?)
;; "You are unaffiliated, in the wilderness."

(federation?)
;; "You are not part of any confederation.
;;  No peers discovered."
```

---

## 6. Design Rationale

The Wilderness serves multiple purposes:

1. **Honest onboarding** - Users know they are not yet part of anything
2. **Unified metaphor** - Same space for unaffiliated and wormhole transit
3. **Security clarity** - No implicit trust, no assumed identity
4. **Poetic resonance** - Evokes the uncertainty of the unaffiliated state

---

## 7. References

1. Angleton, J.J. - "Wilderness of Mirrors" (intelligence terminology)
2. Eliot, T.S. - "Gerontion" (original source of the phrase)
3. RFC-010 - Federation Protocol
4. RFC-044 - Node Enrollment

---

## Changelog

- **2026-01-10** - Initial specification

---

*In the wilderness, all are equal. None are trusted. Until proven otherwise.*
