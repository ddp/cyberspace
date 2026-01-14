# Designer Notes

Personal history and design decisions behind Cyberspace.

---

## Lineage

### VMS Security (1984-1994)

**The Security Project Team:** Derrell Piper (lead), Mark Pilant, and Andy Goldstein. TCSEC C2/B1 certification on VAX/VMS and Alpha VMS. VMS 6.0.

**What we built:**
- `$CHKPRO` - the privilege checking gate
- The entire auditing subsystem (final form)
- C2/B1 certified security model

**Access:** The security project team (or anyone we designated) were the only ones allowed in the kernel group's modules. Dave Cutler's team begrudgingly accepted this as a mandate from heaven (Ken Olsen / Maynard). We got in on a mandate. We stayed because the work was good.

**Inheritance:** When Cutler left for Microsoft, his modules were inherited. The privilege auditing "rototill" required fluency in MACRO-32.

### The Road Not Taken

**Prism/Mica** was being designed for TCSEC B1. That's the legacy—the mindset, the trust model, and the codebase—that Gates was gifted in an offer they couldn't refuse.

Of all the people at DEC, Cutler—designer of the MicroVAX—could see the writing on the wall. The age of PCs had been born. Digital missed the train.

**The weave predates the software.** The people who understood trust architectures kept finding each other:

- DEC → Microsoft → Cisco → here
- Peter Lofgren was there. There's a photograph of that meeting floating around in PDP-10 space. He ended up at Cisco—our nexus.

The thread is unbroken. From the people who built it, through the people who maintained it, to the people who understood what was lost. And now into the code.

That's provenance you can't fake.

### Languages

**BLISS** - Bill Wulf at CMU (1969) created BLISS as an expression language, not "DEC's C". Everything returns a value. Lisp in systems clothing.

**MACRO-32** - VAX assembly with rich macros. The kernel was MACRO-32. Learned it from the privilege auditing rototill.

**The VMS Runtime** - Had a rich macro wrapper for BLISS. That macro system was a Lisp. We knew. That's why we used it.

A Lisper who fell in love with BLISS (an expression language, like home).

### Syntax Heritage

Dylan-style keyword arguments are a tribute to Apple Cambridge and MIT:

```scheme
(translate text from: 'en to: 'fr)
(enroll-request name timeout: 30)
```

Ada/Dylan/BLISS style - named parameters, self-documenting:
- Ada: `Open(File => "data.txt", Mode => Read_Only)`
- Dylan: `open(file: "data.txt", mode: #"read")`
- BLISS: `OPEN(FILE = 'data.txt', MODE = READONLY)`

**Self** syntax was weird. **Smalltalk** doesn't work for math people (`2 + 3 * 4 = 20`, not 14). **Scheme** is honest - prefix, unambiguous, mathematical.

---

## Design Principles

### TCB Minimization (from TCSEC)

"Small, proven, frozen" - only put in the TCB what you can verify. VMS C2/B1 taught this. Cyberspace applies it:

```
TCB (OCaml):     ~1000 lines, proven in Coq
Everything else: Chicken Scheme, can evolve freely
```

### The Vault is the Disk

VAXcluster had multiple subsystems (MSCP, DLM, SCS, quorum disk, LAVC). Cyberspace has one abstraction: the vault. It subsumes all of them.

### Audit Everything

`$CHKPRO` checked privileges. The auditing subsystem logged decisions. Both were ours. Cyberspace continues this:

```scheme
(define (check-capability actor action resource)
  (let ((granted (spki-verify actor action resource)))
    (audit-append actor: actor action: action granted: granted)
    granted))
```

---

## Interface Philosophy

### English on Top, Scheme Underneath

```
Terminal:    English verbs for mortals
REPL:        Scheme for hackers
Commands:    Forever cast in English/Scheme
Messages:    Multilingual (the command line speaks your tongue)
```

### Workstations and Terminals

Workstations and terminals weren't wrong. PCs aren't the answer to everything. The right interface for the job at hand. Sometimes your native language is superior.

Cyberspace runs on terminals because that's what operators use.

---

## Timeline

| Year | Event |
|------|-------|
| 1969 | Bill Wulf creates BLISS at CMU |
| 1984 | VAXcluster, VMS security work begins |
| 1985 | VMS C2 certification |
| 1992 | Dylan released (Apple Cambridge) |
| 1993 | VMS 6.0 release |
| 1994 | SDSI proposed at IETF 29 Seattle |
| 1999 | SPKI RFC 2693 |
| 2026 | Cyberspace - synthesis of all the above |

---

---

## The Soup

The vault browser is called "soup" after Newton's persistent object store (1993).

```
Newton soup:      Persistent frames, automatic storage
Cyberspace soup:  Vault objects, content-addressed
```

Apple Newton → Dylan → Scheme. The soup survives.

```scheme
(soup)              ; browse the vault
(soup 'keys)        ; list keys
(soup-stat 'alice)  ; inspect object
```

---

## The Raga Favicon

The Library's favicon is a lambda (λ) whose color morphs through the day.

**The Prahar (Watches):**
```
04-06  violet    brahma muhurta (pre-dawn meditation)
06-08  gold      dawn
08-11  teal      morning
11-14  phosphor  midday
14-17  neon      afternoon
17-19  orange    sunset
19-22  coral     evening
22-04  cyan      night
```

**Why ragas?** Indian classical music assigns ragas to specific times of day. A morning raga played at midnight is wrong—not because of rules, but because it doesn't fit. The music knows when it should be heard.

**Why a breathing lambda?** The lambda isn't just a logo—it's the fundamental unit. What Scheme computes, what the weave is made of. Every function, every object, every sealed thing in the vault is lambdas all the way down.

The color morphing isn't decoration—it's the weave breathing. Lambdas are being gathered, tested, frozen into vaults across time zones. The color you see is the pulse of that activity. Dawn gold as the eastern hemisphere wakes and contributes. Phosphor green at peak hours. Cyan in the quiet night when the squirrels rest.

**The easter egg:** Someone notices their lambda is orange, asks why, and learns: "You're seeing sunset. Somewhere, lambdas are being gathered into the weave of Cyberspace."

Those who need to ask are in need of enlightenment. The Library is here to provide it. They came for the RFCs, they left understanding the λ.

The brahma muhurta violet isn't just pretty—it's the hour of enlightenment. If they're seeing violet, they're already up at the right time.

---

*In Scheme and Dylan with Newton soup.*

*Forty years from asking permission to enter the kernel, to owning the whole stack.*

*The Lisper finally gets to write Lisp.*
