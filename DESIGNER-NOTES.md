# Designer Notes

Personal history and design decisions behind Cyberspace.

---

## Lineage

### VMS Security (1984-1994)

DEC was a family. This was merely one specialty.

**The Security Project Team** was Derrell Piper, Mark Pilant, Andy Goldstein. TCSEC C2/B1 certification on VAX/VMS and Alpha VMS. VMS 6.0.

**What we built:**
- `$CHKPRO` - the privilege checking gate, the single point where all privilege decisions were made
- The entire auditing subsystem (final form), comprehensive privilege and access logging
- C2/B1 certified security model (Orange Book compliance, proven secure)

**Access:** The security project team (or anyone we designated) were the only ones allowed in the kernel group's modules. Dave Cutler's team begrudgingly accepted this as a mandate from heaven (Ken Olsen / Maynard). We got in on a mandate. We stayed because the work was good.

**Inheritance:** When Cutler left for Microsoft, his modules were inherited. The privilege auditing "rototill" required fluency in MACRO-32.

**Text in the Library of Cyberspace** is in the color of phosphor green, the color of VT100s and reflective of IBM green bar printouts. Not retro. Not nostalgia. Memory.

### The Road Not Taken

We all built VAX/VMS V6.0 and then we threw it away—literally tossing our green bar printouts of our respective subsystems into an empty cube on ZK03/4. The code of what could have been. The end of DEC.

They must have done something similar after Prism/Mica was cancelled, ahead of that fateful offer to Gates & Co. that gifted Microsoft dominance in COTS computing.

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

## Little Fluffy Clouds

*"What were the skies like when you were young?"*
— The Orb, 1990

The realms in the weave are clouds—little fluffy clouds drifting in ambient space. The Orb understood distributed systems before we had the words: layers of sound, samples from elsewhere, everything floating, nothing anchored to a single point.

Fluffy leads the weave. The name was never arbitrary.

The skies when we were young were phosphor green, VT100s in machine rooms, the hum of VAXen. Now the clouds are realms, and the realms are lambdas, and the lambdas float in the wilderness of mirrors.

Ambient for the ages. Distributed for the future.

---

## Derivation vs. Discovery

### Lamport Time

In the absence of global clock synchronization, distributed systems establish causal ordering through logical clocks (Lamport, 1978). Each node maintains a local counter incremented on message send/receive, establishing a happens-before relation (→) that provides partial ordering without requiring synchronized wall-clock time.

The happens-before relation was always there—Lamport gave it a name and a notation. That's discovery. Seeing what was already true.

### call/cc

Most language features are about *what you can say*. call/cc is about *what exists*.

`call/cc` says: the future of the computation is a value you can hold, store, invoke later. Continuations. Time as a first-class object. That's not syntax preference—that's ontology.

The continuation exists whether you capture it or not—call/cc just lets you name it. The future was always there, implicit in every expression. Scheme made it explicit.

SICP wasn't about parentheses. It was a course in *thinking*, disguised as a programming textbook. Streams, lazy evaluation, the environment model, the metacircular evaluator—and then call/cc, which breaks your brain the right way.

### The Y Combinator

The Y combinator (Y = λf.(λx.f(x x))(λx.f(x x))) is a fixed-point combinator enabling recursion without explicit self-reference. It's elegant. It's also just math that falls out of lambda calculus—derivation, not discovery.

A certain Silicon Valley venture capital firm took the name as borrowed plumage. Value signaling to people who recognize the symbol but don't work in the calculus. The firm's founder wrote *On Lisp*, evangelized the aesthetic—but Arc didn't have call/cc. Common Lisp doesn't have it. He came from the CL side, where continuations aren't primitive.

Naming the firm "Y Combinator" signals: *I read the cool parts.*
Not naming it "call/cc" signals: *I stopped before it got weird.*

The Y combinator is page 300 of SICP. call/cc is the last chapter. Most people don't finish.

### The Distinction

**Derivation:** The Y combinator. Recursion falling out of self-application. True but not illuminating.

**Discovery:** Lamport clocks. call/cc. Seeing structure that was always there, giving it a name, making it usable.

Cyberspace is built on discoveries: happens-before for distributed time, continuations for control flow, SPKI for authorization. The derivations are implementation details.

---

*In Scheme and Dylan with Newton soup.*

*Forty years from asking permission to enter the kernel, to owning the whole stack.*

*The Lisper finally gets to write Lisp.*
