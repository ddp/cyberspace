;; RFC-058: Designer Notes
;; Loch Lambda - the depths of the weave

(rfc
  (number 58)
  (title "Designer Notes")
  (subtitle "Loch Lambda")
  (status "Living Document")
  (date "January 2026")

  (section
    "Abstract"
    (p "Personal history, design decisions, and accumulated wisdom from building Cyberspace. This RFC grows as the weave deepens."))

  (section
    "1. Lineage"

    (subsection
      "1.1 VMS Security (1984-1994)"
      (p "The designer was engineering lead for TCSEC C2/B1 certification on VAX/VMS and Alpha VMS, and owned the VMS 6.0 release.")
      (p "The Security Project Team: Derrell Piper, Mark Pilant, Andy Goldstein.")
      (p "What we built:")
      (list
        (item "$CHKPRO - the privilege checking gate")
        (item "The entire auditing subsystem (final form)")
        (item "C2/B1 certified security model"))
      (p "When Cutler left for Microsoft, his modules were inherited. The privilege auditing rototill required fluency in MACRO-32."))

    (subsection
      "1.2 TGV and IPsec (1994-2001)"
      (p "After DEC, the designer joined TGV Inc. (MultiNet TCP/IP for VMS). Designed all of Secure/IP and the Kerberized VAX/VMS SSO using Kerberos.")
      (p "Cisco acquired TGV in 1996, thinking they were buying a Windows TCP/IP stack. They weren't. MultiNet was VMS networking; the Windows products were incidental.")
      (p "The IPsec/IKE work continued through Network Alchemy (acquired by Nokia). The designer authored " (link "draft-ietf-ipsec-isakmp-gss-auth-07" "https://www.yoyodyne.com/ddp/draft-ietf-ipsec-isakmp-gss-auth-07.txt") ", 'A GSS-API Authentication Method for IKE', which documented how to authenticate IKE using Kerberos over GSS-API.")
      (p "Brian Swander was added as co-author to hand the specification to Microsoft for Windows 2000 implementation. The Vendor Payload extension mechanism in IKE was added to encapsulate Microsoft's GSS-API extension cleanly.")
      (p "That same Vendor Payload mechanism was later used extensively in AlchemyOS for proprietary extensions without breaking interoperability. Good protocol design: create a generic extension point for one use case, it becomes useful for everyone.")
      (p "The path: DEC → TGV → Cisco → Network Alchemy → Nokia, carrying IPsec/IKE expertise through each transition. The work survives in Windows cross-realm domain authentication to this day.")
      (p "Acknowledgments for the NT IPsec/IKE work: George Lake, Rob Adams, Max Pritikin, John [TODO], Anne Church, Peter Ford, and William Dixon who cat herded IPv6 into existence during NT5 (Windows 2000) development."))

    (subsection
      "1.3 Languages"
      (p "BLISS - Bill Wulf at CMU (1969) created BLISS as an expression language, not 'DEC's C'. Everything returns a value. Lisp in systems clothing.")
      (p "MACRO-32 - VAX assembly with rich macros. The kernel was MACRO-32.")
      (p "The VMS Runtime - Had a rich macro wrapper for BLISS. That macro system was a Lisp. We knew.")
      (p "The designer came to VMS as a Lisper, fell in love with BLISS (an expression language, like home)."))

    (subsection
      "1.4 Syntax Heritage"
      (p "Dylan-style keyword arguments are a tribute to Apple Cambridge and MIT:")
      (code scheme "(translate text from: 'en to: 'fr)
(enroll-request name timeout: 30)")
      (p "Self syntax was weird. Smalltalk doesn't work for math people. Scheme is honest - prefix, unambiguous, mathematical."))

    (subsection
      "1.5 System Service Vocabulary"
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
      (p "The original $IMPERSONATION framework was authored by Rich Bouchard. It was lost during the Mitnick incidents when Andy Goldstein and I decided we needed to rebuild our compiler chain from known good offsite backups - with Ken Thompson's 'Reflections on Trusting Trust' fresh in our minds. In doing so, we lost a year of development during Alpha, including the original kernel threads implementation and the $IMPERSONATION framework.")))

  (section
    "2. Design Principles"

    (subsection
      "2.1 TCB Minimization"
      (p "From TCSEC: 'Small, proven, frozen' - only put in the TCB what you can verify.")
      (code "TCB (OCaml):     ~1000 lines, proven in Coq
Everything else: Chicken Scheme, can evolve freely"))

    (subsection
      "2.2 The Vault is the Disk"
      (p "VAXcluster had multiple subsystems (MSCP, DLM, SCS, quorum disk, LAVC). Cyberspace has one abstraction: the vault. It subsumes all of them."))

    (subsection
      "2.3 Audit Everything"
      (p "$CHKPRO checked privileges. The auditing subsystem logged decisions. Both were ours. Cyberspace continues this.")))

  (section
    "3. The Soup"
    (p "The vault browser is called 'soup' after Newton's persistent object store (1993).")
    (code "Newton soup:      Persistent frames, automatic storage
Cyberspace soup:  Vault objects, content-addressed")
    (p "Apple Newton -> Dylan -> Scheme. The soup survives."))

  (section
    "4. The Raga Favicon"
    (p "The Library's favicon is a lambda whose color morphs through the day.")

    (subsection
      "4.1 The Prahar (Watches)"
      (code "04-06  violet    brahma muhurta (pre-dawn meditation)
06-08  gold      dawn
08-11  teal      morning
11-14  phosphor  midday
14-17  neon      afternoon
17-19  orange    sunset
19-22  coral     evening
22-04  cyan      night"))

    (subsection
      "4.2 Why Ragas?"
      (p "Indian classical music assigns ragas to specific times of day. A morning raga played at midnight is wrong - not because of rules, but because it doesn't fit. The music knows when it should be heard."))

    (subsection
      "4.3 Why a Breathing Lambda?"
      (p "The lambda isn't just a logo - it's the fundamental unit. What Scheme computes, what the weave is made of. Every function, every object, every sealed thing in the vault is lambdas all the way down.")
      (p "The color morphing isn't decoration - it's the weave breathing. Lambdas are being gathered, tested, frozen into vaults across time zones. The color you see is the pulse of that activity."))

    (subsection
      "4.4 The Easter Egg"
      (p "Someone notices their lambda is orange, asks why, and learns: 'You're seeing sunset. Somewhere, lambdas are being gathered into the weave of Cyberspace.'")
      (p "Those who need to ask are in need of enlightenment. The Library is here to provide it. They came for the RFCs, they left understanding the lambda.")
      (p "The brahma muhurta violet isn't just pretty - it's the hour of enlightenment. If they're seeing violet, they're already up at the right time.")))

  (section
    "5. Weaving by Lambda"
    (p "Weaving by lambda - the craft. The act of building, creating, adding to Cyberspace.")
    (p "Loch lambda - the measure of depth achieved. How far have you gone? How much have you woven?")
    (p "The deeper you weave, the more loch lambda you've earned. A merit badge for the depths explored.")
    (p "The weave thickens as lambdas accrete. Each function, each object, each sealed thing adds to the fabric. The loch deepens.")
    (p "The pun layers: LOC (lines of code) -> loc/lambda (lambdas as unit) -> loch lambda (the depths).")
    (p "Zen is below 10. Enlightened code is under 10 loc/lambda. Small, focused, one thing done well."))

  (section
    "6. Format Philosophy"
    (p "The web forgot that good enough is good enough.")
    (p "JPEG worked. PNG worked. FLAC worked. But someone always needs 3% better compression at the cost of yet another decoder in every browser, another format to support forever, another thing that might not render in ten years.")
    (p "Plan 9 had one image format. Unix had pipes and text. Lisp has s-expressions. The power comes from composing a few things well, not accumulating special cases.")
    (p "SVG is in the right spirit - just XML describing geometry. The browser already has the renderer. No new codec, no binary blob, no patent minefield.")
    (p "The dumb web optimizes for benchmarks. The good web optimizes for durability."))

  (section
    "7. Human Interface Principles"

    (subsection
      "7.1 Output Philosophy"
      (list
        (item "Silence is default - Success prints nothing. Failure is an error.")
        (item "No developer notes - If it's not for the user, it doesn't print.")
        (item "Verbose is opt-in - --verbose for play-by-play, otherwise quiet.")
        (item "Consequential operations may announce - Enrollment, federation changes, realm joins.")))

    (subsection
      "7.2 Async Model"
      (list
        (item "Prompts return frequently, don't block on long operations.")
        (item "Background work runs async, notify on completion.")
        (item "Notifications are optional - check when you want, never modal, never blocking.")
        (item "Your response is never required.")))

    (subsection
      "7.3 Introspection by Semantic Type"
      (p "Not a generic notification queue. Organized by type of operation: enrollments, syncs, votes, federation requests. Each reflected where it makes sense. Introspect by what it *is*, not dig through a queue."))

    (subsection
      "7.4 Governance"
      (p "Passive consent: silence is assent to federation consensus. If you don't vote, you live with the federation's decision. Fork your own security policy in your realm if you disagree."))

    (subsection
      "7.5 VMS Lessons"
      (list
        (item "$FAO-style formatted output for the TCB - clean ASCII.")
        (item "No calling the runtime from the TCB.")
        (item "The audit and protected subsystems live in their own UI layer.")))

    (subsection
      "7.6 Help Command Behavior"
      (p "/?/ (and help variants) should always be useful across the REPL. When there's nothing contextual to offer, still try to be helpful - offer general guidance, suggest related commands, or at minimum apologize for not being able to offer specific help.")))

  (section
    "Changelog"
    (p "- 2026-01-13 - Section 1.2 TGV and IPsec: Secure/IP, GSS-API/IKE draft, Vendor Payload, AlchemyOS")
    (p "- 2026-01-13 - Rich Bouchard, $IMPERSONATION, Mitnick, Trusting Trust")
    (p "- 2026-01-13 - Section 1.5 System Service Vocabulary (CHP$_*, $PERSONA_*)")
    (p "- 2026-01-13 - Section 7 Human Interface Principles")
    (p "- 2026-01-13 - Weaving by lambda, loch lambda as merit")
    (p "- 2026-01-13 - Initial specification, migrated from DESIGNER-NOTES.md")))
