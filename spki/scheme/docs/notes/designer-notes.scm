;; Designer Notes
;; Loch Lambda - the depths of the weave

(document
  (title "Designer Notes")
  (subtitle "Loch Lambda")
  (status "Living Document")
  (date "January 2026")
  (author "Derrell Piper" "ddp@eludom.net")

  (section
    "Abstract"
    (p "Personal history and design decisions behind Cyberspace. This document grows as the weave deepens."))

  (section
    "1. Lineage"

    (subsection
      "1.1 VMS Security (1984-1994)"
      (p "DEC was a family. This was merely one specialty.")
      (p "The Security Project Team was Derrell Piper, Mark Pilant, Andy Goldstein. TCSEC C2/B1 certification on VAX/VMS and Alpha VMS. VMS 6.0.")
      (p "What we built:")
      (list
        (item "$CHKPRO - the privilege checking gate, the single point where all privilege decisions were made")
        (item "The entire auditing subsystem (final form), comprehensive privilege and access logging")
        (item "C2/B1 certified security model (Orange Book compliance, proven secure)"))
      (p "Access: The security project team (or anyone we designated) were the only ones allowed in the kernel group's modules. Dave Cutler's team begrudgingly accepted this as a mandate from heaven (Ken Olsen // Maynard). We got in on a mandate. We stayed because the work was good.")
      (p "Inheritance: When Cutler left for Microsoft, his modules were inherited. The privilege auditing 'rototill' required fluency in MACRO-32.")
      (p "Text in the Library of Cyberspace is in the color of phosphor green, the color of VT100s and reflective of IBM green bar printouts. Not retro. Not nostalgia. Memory."))

    (subsection
      "1.2 The Road Not Taken"
      (p "We all built VAX/VMS V6.0 and then we threw it away--literally tossing our green bar printouts of our respective subsystems into an empty cube on ZK03/4. The code of what could have been. The end of DEC.")
      (p "They must have done something similar after Prism/Mica was cancelled, ahead of that fateful offer to Gates & Co. that gifted Microsoft dominance in COTS computing.")
      (p "Prism/Mica was being designed for TCSEC B1. That's the legacy--the mindset, the trust model, and the codebase--that Gates was gifted in an offer they couldn't refuse.")
      (p "Of all the people at DEC, Cutler--designer of the MicroVAX--could see the writing on the wall. The age of PCs had been born. Digital missed the train.")
      (p "The weave predates the software. The people who understood trust architectures kept finding each other:")
      (list
        (item "DEC -> Microsoft -> Cisco -> here")
        (item "Peter Lofgren was there. There's a photograph of that meeting floating around in PDP-10 space. He ended up at Cisco--our nexus."))
      (p "The thread is unbroken. From the people who built it, through the people who maintained it, to the people who understood what was lost. And now into the code.")
      (p "That's provenance you can't fake."))

    (subsection
      "1.3 Languages"
      (p "BLISS - Bill Wulf at CMU (1969) created BLISS as an expression language, not 'DEC's C'. Everything returns a value. Lisp in systems clothing.")
      (p "MACRO-32 - VAX assembly with rich macros. The kernel was MACRO-32. Learned it from the privilege auditing rototill.")
      (p "The VMS Runtime - Had a rich macro wrapper for BLISS. That macro system was a Lisp. We knew. That's why we used it.")
      (p "A Lisper who fell in love with BLISS (an expression language, like home)."))

    (subsection
      "1.4 System Service Vocabulary"
      (p "The VMS system service vocabulary provides the conceptual heritage for Cyberspace's security primitives.")
      (p "The security subsystem was written exclusively in BLISS (with MACRO-32 fluency for reading the layers beneath). Now it's Scheme.")
      (p "Access check pattern:")
      (code "$CREATE_USER_PROFILE  →  builds encoded user security profile
        ↓
$CHKPRO / $CHECK_ACCESS  →  evaluates access using profile + object protection
        ↓
SS$_NORMAL / SS$_NOPRIV  →  grant or deny")
      (p "Key item codes (CHP$_*):")
      (list
        (item "CHP$_ACCESS → access-mask (requested access type bitmask)")
        (item "CHP$_PROT → protection (SOGW protection mask)")
        (item "CHP$_OWNER → owner (object owner identifier)")
        (item "CHP$_UIC → principal (accessor's identity)")
        (item "CHP$_PRIV → privileges (privilege mask)")
        (item "CHP$_ACL → acl (access control list)")
        (item "CHP$_FLAGS → flags (check options: observe/alter)"))
      (p "Flags: CHP$V_AUDIT → audit?, CHP$V_OBSERVE → read?, CHP$V_ALTER → write?")
      (p "Return status: SS$_NORMAL → #t, SS$_NOPRIV → #f, SS$_ACCVIO → 'accvio, SS$_IVACL → 'invalid-acl")
      (p "Impersonation ($PERSONA_*): Used by DECdfs and distributed file services to act on behalf of remote clients without re-implementing access checks.")
      (p "$PERSONA was designed by the DEC Distributed File System group, not VMS Engineering.")
      (p "The original $IMPERSONATION framework was authored by myself with Rich Bouchard. It was lost during the Mitnick incidents when Andy Goldstein and I decided we needed to rebuild our compiler chain from known good offsite backups - with Ken Thompson's 'Reflections on Trusting Trust' fresh in our minds. In doing so, we lost a year of development during Alpha, including the original kernel threads implementation and the $IMPERSONATION framework."))

    (subsection
      "1.5 Syntax Heritage"
      (p "Dylan-style keyword arguments are a tribute to Apple Cambridge and MIT:")
      (code scheme "(translate text from: 'en to: 'fr)
(enroll-request name timeout: 30)")
      (p "Ada/Dylan/BLISS style - named parameters, self-documenting:")
      (list
        (item "Ada: Open(File => \"data.txt\", Mode => Read_Only)")
        (item "Dylan: open(file: \"data.txt\", mode: #\"read\")")
        (item "BLISS: OPEN(FILE = 'data.txt', MODE = READONLY)"))
      (p "Self syntax was weird. Smalltalk doesn't work for math people (2 + 3 * 4 = 20, not 14). Scheme is honest - prefix, unambiguous, mathematical.")))

  (section
    "2. Design Principles"

    (subsection
      "2.1 TCB Minimization"
      (p "From TCSEC: 'Small, proven, frozen' - only put in the TCB what you can verify. VMS C2/B1 taught this. Cyberspace applies it:")
      (code "TCB (OCaml):     ~1000 lines, proven in Coq
Everything else: Chicken Scheme, can evolve freely"))

    (subsection
      "2.2 The Vault is the Disk"
      (p "VAXcluster had multiple subsystems (MSCP, DLM, SCS, quorum disk, LAVC). Cyberspace has one abstraction: the vault. It subsumes all of them."))

    (subsection
      "2.3 Audit Everything"
      (p "$CHKPRO checked privileges. The auditing subsystem logged decisions. Both were ours. Cyberspace continues this:")
      (code scheme "(define (check-capability actor action resource)
  (let ((granted (spki-verify actor action resource)))
    (audit-append actor: actor action: action granted: granted)
    granted))")))

  (section
    "3. Interface Philosophy"

    (subsection
      "3.1 English on Top, Scheme Underneath"
      (code "Terminal:    English verbs for mortals
REPL:        Scheme for hackers
Commands:    Forever cast in English/Scheme
Messages:    Multilingual (the command line speaks your tongue)"))

    (subsection
      "3.2 For the Uninitiated"
      (code scheme "(about)      ; What is this place?
(huh?)       ; Same question, different inflection
(what?)      ; Still the same
(describe)   ; For the formal")
      (p "The answer morphs with the weave. Standing alone, it suggests enrollment. With peers, it lists them. The description reflects the current state--not a static brochure but a living mirror of the constellation.")
      (p "Cyberspace is a system for storing and sharing digital documents, code, and data without relying on any company, government, or central authority. Instead of trusting a corporation to keep your files safe, you and people you trust keep copies that are cryptographically signed--meaning anyone can verify who created something and that it hasn't been tampered with. If one computer goes offline, the others still have everything. Your data belongs to you, verified by math, preserved by the people you choose."))

    (subsection
      "3.3 Workstations and Terminals"
      (p "Workstations and terminals weren't wrong. PCs aren't the answer to everything. The right interface for the job at hand. Sometimes your native language is superior.")
      (p "Cyberspace runs on terminals because that's what operators use."))

    (subsection
      "3.4 The Period as Imperative (Smalltalk Heritage)"
      (p "In Smalltalk, the period terminates a statement. It's the moment of commitment--everything before it is preparation, the period makes it so.")
      (p "Cyberspace borrows this: any command suffixed with '.' implies execution and propagation. 'commit.' means commit and sync. 'fix.' means fix and make it so.")
      (code "commit    → stage the intention
commit.   → stage, execute, propagate to the weave")
      (p "The period is not punctuation. It's the imperative mood. Smalltalk understood that the moment of action deserves its own syntax."))

    (subsection
      "3.5 Do All the Th[i,a]nga"
      (p "The full toolchain invocation: commit, push, regen-all, publish. An idea isn't complete until it's self-contained and self-documenting in the weave.")
      (code "thinga := commit → push → regen-all → publish")
      (p "regen-all is the totality of sanity checking before publishing: recompile all modules, verify types, run tests, regenerate documentation. Nothing reaches the weave without passing the scrutinizer--a nod to Felix Winkelmann's CHICKEN Scheme, whose scrutinizer catches what the programmer misses. It has more inference because it's in lambda.")
      (p "The spelling nods to both 'things' and 'thanga' (Tamil: gold). Ideas forged through the full cycle become permanent--golden artifacts in the weave.")
      (p "Partial work stays local. Published work is proven. The toolchain is the crucible.")))

  (section
    "4. The Soup"
    (p "The vault browser is called 'soup' after Newton's persistent object store (1993).")
    (code "Newton soup:      Persistent frames, automatic storage
Cyberspace soup:  Vault objects, content-addressed")
    (p "Apple Newton -> Dylan -> Scheme. The soup survives.")
    (code scheme "(soup)              ; browse the vault
(soup 'keys)        ; list keys
(soup-stat 'alice)  ; inspect object"))

  (section
    "5. The Raga Favicon"
    (p "The Library's favicon is a lambda whose color morphs through the day.")

    (subsection
      "5.1 The Prahar (Watches)"
      (code "04-06  violet    brahma muhurta (pre-dawn meditation)
06-08  gold      dawn
08-11  teal      morning
11-14  phosphor  midday
14-17  neon      afternoon
17-19  orange    sunset
19-22  coral     evening
22-04  cyan      night"))

    (subsection
      "5.2 Why Ragas?"
      (p "Indian classical music assigns ragas to specific times of day. A morning raga played at midnight is wrong--not because of rules, but because it doesn't fit. The music knows when it should be heard."))

    (subsection
      "5.3 Why a Breathing Lambda?"
      (p "The lambda isn't just a logo--it's the fundamental unit. What Scheme computes, what the weave is made of. Every function, every object, every sealed thing in the vault is lambdas all the way down.")
      (p "The color morphing isn't decoration--it's the weave breathing. Lambdas are being gathered, tested, frozen into vaults across time zones. The color you see is the pulse of that activity. Dawn gold as the eastern hemisphere wakes and contributes. Phosphor green at peak hours. Cyan in the quiet night when the squirrels rest."))

    (subsection
      "5.4 The Easter Egg"
      (p "Someone notices their lambda is orange, asks why, and learns: 'You're seeing sunset. Somewhere, lambdas are being gathered into the weave of Cyberspace.'")
      (p "Those who need to ask are in need of enlightenment. The Library is here to provide it. They came for the RFCs, they left understanding the lambda.")
      (p "The brahma muhurta violet isn't just pretty--it's the hour of enlightenment. If they're seeing violet, they're already up at the right time.")))

  (section
    "6. Little Fluffy Clouds"
    (p "'What were the skies like when you were young?' -- The Orb, 1990")
    (p "The realms in the weave are clouds--little fluffy clouds drifting in ambient space. The Orb understood distributed systems before we had the words: layers of sound, samples from elsewhere, everything floating, nothing anchored to a single point.")
    (p "Fluffy leads the weave. The name was never arbitrary.")
    (p "The skies when we were young were phosphor green, VT100s in machine rooms, the hum of VAXen. Now the clouds are realms, and the realms are lambdas, and the lambdas float in the wilderness of mirrors.")
    (p "Ambient for the ages. Distributed for the future."))

  (section
    "7. Derivation vs. Discovery"

    (subsection
      "7.1 Lamport Time"
      (p "In the absence of global clock synchronization, distributed systems establish causal ordering through logical clocks (Lamport, 1978). Each node maintains a local counter incremented on message send/receive, establishing a happens-before relation that provides partial ordering without requiring synchronized wall-clock time.")
      (p "The happens-before relation was always there--Lamport gave it a name and a notation. That's discovery. Seeing what was already true."))

    (subsection
      "7.2 call/cc"
      (p "Most language features are about what you can say. call/cc is about what exists.")
      (p "call/cc says: the future of the computation is a value you can hold, store, invoke later. Continuations. Time as a first-class object. That's not syntax preference--that's ontology.")
      (p "The continuation exists whether you capture it or not--call/cc just lets you name it. The future was always there, implicit in every expression. Scheme made it explicit.")
      (p "SICP wasn't about parentheses. It was a course in thinking, disguised as a programming textbook. Streams, lazy evaluation, the environment model, the metacircular evaluator--and then call/cc, which breaks your brain the right way."))

    (subsection
      "7.3 The Y Combinator"
      (p "The Y combinator (Y = λf.(λx.f(x x))(λx.f(x x))) is a fixed-point combinator enabling recursion without explicit self-reference. It's elegant. It's also just math that falls out of lambda calculus--derivation, not discovery.")
      (p "A certain Silicon Valley venture capital firm took the name as borrowed plumage. Value signaling to people who recognize the symbol but don't work in the calculus. The firm's founder wrote 'On Lisp', evangelized the aesthetic--but Arc didn't have call/cc. Common Lisp doesn't have it. He came from the CL side, where continuations aren't primitive.")
      (p "Naming the firm 'Y Combinator' signals: I read the cool parts. Not naming it 'call/cc' signals: I stopped before it got weird.")
      (p "The Y combinator is page 300 of SICP. call/cc is the last chapter. Most people don't finish."))

    (subsection
      "7.4 The Distinction"
      (p "Derivation: The Y combinator. Recursion falling out of self-application. True but not illuminating.")
      (p "Discovery: Lamport clocks. call/cc. Seeing structure that was always there, giving it a name, making it usable.")
      (p "Cyberspace is built on discoveries: happens-before for distributed time, continuations for control flow, SPKI for authorization. The derivations are implementation details.")))

  (section
    "8. Timeline"
    (code "1969  Bill Wulf creates BLISS at CMU
1984  VAXcluster, VMS security work begins
1985  VMS C2 certification
1992  Dylan released (Apple Cambridge)
1993  VMS 6.0 release
1994  SDSI proposed at IETF 29 Seattle
1999  SPKI RFC 2693
2026  Cyberspace - synthesis of all the above"))

  (section
    "Closing"
    (p "In Scheme and Dylan with Newton soup.")
    (p "Forty years from asking permission to enter the kernel, to owning the whole stack.")
    (p "The Lisper finally gets to write Lisp.")))
