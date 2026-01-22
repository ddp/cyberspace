;; Memo-0009: Designer Notes
;; Intellectual heritage and design philosophy (not an RFC)

(memo
  (number 9)
  (title "Designer Notes")
  (status "Draft")
  (date "2026-01-22T04:31:00Z")
  (author "Derrell Piper" "ddp@eludom.net")

  (section
    "Notice"
    (p "This is a living document, not a specification. It records the intellectual heritage, design philosophy, and collaborative process behind Cyberspace."))

  (section
    "1. Intellectual Heritage"

    (subsection
      "1.1 MIT Athena and SPKI"
      (p "Cyberspace traces its lineage to MIT's Project Athena and the Simple Public Key Infrastructure (SPKI) work that emerged from MIT and the Internet Engineering Task Force (IETF).")
      (p "Athena (1983-1991) introduced Kerberos, distributed authentication, and the concept of a unified computing environment across heterogeneous systems. Digital Equipment Corporation (DEC) funded Athena and contributed workstations.")
      (p "Two independent threads merged at IETF to form SDSI/SPKI:")
      (list
        (item "Simple Distributed Security Infrastructure (SDSI) - Ron Rivest at MIT, focusing on naming and local name spaces")
        (item "SPKI - Carl Ellison at IETF, focusing on authorization and capabilities"))
      (p "Ellison's SPKI RFCs (2693, 2692) formalized capability-based authorization through certificate chains. When IETF standardized this work, Rivest's SDSI naming merged in. The result (SDSI/SPKI 2.0) gave us both authorization and naming.")
      (p "These ideas were absorbed during the same lamport epoch as R4RS Scheme (1991) and SDSI (1996), alongside the practical education of Boston traffic negotiation - both exercises in asserting authority without central coordination."))

    (subsection
      "1.2 Why Scheme"
      (p "Scheme was chosen because its homoiconic S-expressions make the representation of programs and structured data the same kind of thing. One parser, one set of tools works uniformly over code, certificates, audit trails, and configuration.")
      (p "In a homoiconic language, the primary representation of programs is also a data structure in a primitive type of the language. Scheme uses S-expressions—nested lists and atoms—as both surface syntax and natural tree-shaped data. The abstract syntax tree and textual form closely align.")
      (p "The same reader parses program text, configuration records, and application data into a single uniform format. Certificates, audit records, memos, and code are all S-expressions manipulated with the same combinators:")
      (code scheme ";; All the same representation
(read)           ; parse code
(read-cert)      ; parse certificate
(read-audit)     ; parse audit trail
(kwic 'soup)     ; search memos")
      (p "One minimal, well-specified parser eliminates impedance mismatches between code format and data format. No JSON-to-object mapping. No protobuf schema compiler. Structures representing policies look exactly like structures representing the code enforcing them.")
      (p "When you (kwic 'soup) you search S-expressions with S-expressions. The memos are data. The code is data. The boundary dissolves.")
      (p "The language that Abelson and Sussman used to teach computational thinking at MIT is the same language used to implement the security architecture that MIT research defined. Full circle.")
      (p "Cyberspace Scheme is intentionally R5RS and R7RS-small, following CHICKEN Scheme's philosophy: a small, portable core with extensions as libraries rather than language features. R5RS (1998) remains the most widely implemented Scheme standard. R7RS-small (2013) preserves that minimalist tradition while adding practical improvements like define-library. The large dialect (R7RS-large, ongoing) is explicitly avoided - complexity belongs in libraries, not the language specification.")
      (p "CHICKEN was chosen over faster implementations (Chez, Racket, Gambit) for its elegance and deployment model. CHICKEN compiles to C, producing standalone executables with no runtime dependencies. The egg system provides a curated library ecosystem. Speed matters less than simplicity when the bottleneck is cryptographic operations in libsodium, not interpreter overhead.")))

  (section
    "2. Collaborative Design"
    (p "Cyberspace was designed in collaboration with Claude (Anthropic), an AI assistant. This collaboration is documented in Memo-056.")
    (p "The interaction model: human provides vision and constraints, AI provides implementation and exploration. Neither could have built this alone."))

  (section
    "3. Naming Coherence"
    (p "Knuth's principle from TAOCP: names should be consistent across the totality of a system. When we renamed 'RFC' to 'Memo' internally, we applied s/rfc/memo/g globally - not just to files being edited, but to every reference in the codebase.")
    (p "Single source of truth extends to terminology. MEMO_NUMBER_WIDTH is defined once; the four-digit format flows from that constant through Scheme and shell. When the namespace overflows to five digits, one change propagates everywhere.")
    (p "Piecemeal renaming creates inconsistent states where variables say one thing and filenames say another. The systematic approach is the only approach."))

  (section
    "4. Target Environments"
    (p "Primary targets:")
    (list
      (item "macOS (Apple Silicon) - Cyberspace.app native shell")
      (item "Linux - including MIT Athena")
      (item "Any POSIX system with CHICKEN Scheme 5.x"))
    (p "The system should feel native on a Mac, work cleanly on Athena, and build anywhere Scheme runs."))

  (section
    "5. The Scheme Beneath"
    (p "Scheme is the implementation language, not the user interface. The novice sees a shell; the schemer sees a REPL. Same system, different lenses.")
    (p "By default, Scheme internals are hidden:")
    (list
      (item "Inspector disabled - errors show simple messages, not debug> prompts")
      (item "Exception display uses plain language, not 'unbound variable'")
      (item "Help shows commands, not S-expressions")
      (item "The : prompt is a portal, not a lambda"))
    (p "Schemers opt in with (enable-inspector!) and see the machinery. The abstraction layer is permeable but not transparent.")
    (p "This is not dumbing down. It is layered revelation - the same principle that makes Cyberspace.app feel native on Mac while running pure Scheme underneath."))

  (section
    "6. The Scrutinizer"
    (p "Consistency requires tooling. The scrutinizer audits tone and terminology across library and code.")
    (p "Two failure modes:")
    (list
      (item "Overreach - poetry where precision needed, whimsy in error messages")
      (item "Underreach - dry jargon where warmth appropriate, internal vocabulary leaking through"))
    (p "Passes:")
    (list
      (item "Vocabulary audit - banned terms in user-facing strings")
      (item "Tone consistency - memos vs help vs errors")
      (item "S-expression exposure - Scheme leaking to surface"))
    (p "Interface:")
    (code scheme "(scrutinize)               ; both passes (default)
(scrutinize 'library)      ; memos only
(scrutinize 'code)         ; code only
(scrutinize #f)            ; disable

*scrutinize-realmtime*     ; parameter, default #f
(scrutinize-realmtime! #t) ; enable during dev")
    (p "Realmtime mode invokes spacetime - scrutiny flows through the realm as time passes. When enabled, violations surface as modules load. Off in production, on in beta."))

  (section
    "7. Forge and Smelter"
    (p "The forge module generates pronounceable passwords using Markov chains on digraph statistics. The lineage traces back to Multics.")

    (subsection
      "7.1 Heritage"
      (p "Original design by Morrie Gasser in PL/1 on Multics. Gasser, author of 'Building a Secure Computer System' (1988), carried the code forward to VAX/VMS where it remained in PL/1 until the Alpha transition.")
      (p "When DEC moved to Alpha architecture, PL/1 wasn't in the initial compiler release. The code had to be expunged from the TCB. Derrell Piper and Jon Callas rewrote it for VMS 6.0 (circa 1991): Piper wrote the BLISS system service for the Trusted Computing Base; Callas wrote the user-mode TPU smelter.")
      (p "US and EU DEC patents were filed on the design (now expired). The terminology - forge, smelter - comes from metallurgy: the smelter refines raw ore (word lists) into workable material (digraph statistics); the forge shapes the final product (pronounceable words).")
      (p "Callas later became a principal author of OpenPGP (RFC 4880) and co-founded PGP Corporation and Silent Circle. He remains a planned beta tester for Cyberspace.")
      (p "The chain of custody: Gasser (Multics PL/1) → Piper/Callas (VMS 6.0 BLISS/TPU) → Cyberspace (Scheme)."))

    (subsection
      "7.2 Design"
      (p "The smelter reads word lists and extracts digraph (character pair) statistics:")
      (list
        (item "Starting pair frequency - which pairs begin words")
        (item "Transition probability - given 'ab', what characters follow")
        (item "Termination markers - which pairs end words"))
      (p "The forge walks these statistics with weighted random selection, producing words that follow the phonetic patterns of the source language. Entropy is tracked in 'decibits' (tenths of bits) to quantify password strength."))

    (subsection
      "7.3 Languages"
      (p "Original VMS languages: English, Latin, Italian, Dutch, Sindarin, Webster. The VT100 diacriticals were encoded in DEC MCS (Multinational Character Set).")
      (p "Cyberspace expansion to 40+ languages follows roughly the operational map of the Office of Strategic Services - another egg for those who recognize the geography:")
      (list
        (item "Western Europe: French, German, Spanish, Portuguese")
        (item "Iberia: Catalan, Galician, Basque")
        (item "Nordic (resistance networks): Swedish, Norwegian, Danish, Finnish")
        (item "Atlantic fringe: Irish, Welsh, Scottish Gaelic, Breton")
        (item "Balkans (partisan country): Greek, Albanian, Serbian, Croatian, Slovenian, Macedonian")
        (item "Eastern front: Polish, Czech, Slovak, Hungarian, Romanian")
        (item "Baltic: Lithuanian, Latvian, Estonian")
        (item "Soviet theater: Russian, Ukrainian, Bulgarian")
        (item "Near East: Turkish, Armenian")
        (item "Mediterranean (George Cross island): Maltese")
        (item "Detachment 101: Vietnamese, Thai, Lao, Korean")
        (item "Literary: Sindarin (Tolkien's Elvish), Dante's Divina Commedia"))
      (p "Word lists sourced from Hunspell, LibreOffice, SCOWL, OpenTaal, Eldamo, and the Princeton Dante Project. All diacriticals converted to UTF-8.")
      (p "Sindarin preserves Tolkien's circumflexes: Manwë, Aulë, Andúril. Dante's medieval Italian sits alongside. The OSS framing is itself an easter egg - layers of meaning for those who dig."))

    (subsection
      "7.4 Related Standards"
      (p "Forge predates but relates to two password generation standards:")
      (list
        (item "FIPS 181 (1993) - Automated Password Generator. Uses trigraph (3-letter) statistics and hyphenation rules. More structured but less natural. Forge's digraph approach (1991) produces smoother results by learning from actual language patterns rather than syllable rules.")
        (item "OPIE/S/Key - One-time Passwords In Everything. Uses a fixed 2048-word dictionary optimized for spoken communication over phone lines. Words are short and phonetically distinct. Different goal: memorability for one-time use vs. pronounceability for permanent passwords."))
      (p "Forge's contribution was combining Markov chain language modeling with entropy tracking - knowing not just that a password sounds right, but exactly how many bits of randomness it contains."))

    (subsection
      "7.5 Interface"
      (code scheme "(forge)              ; one English word
(forge 5)            ; five English words
(forge 'sindarin)    ; one Elvish word
(forge 'latin 3)     ; three Latin words
(forge 'passphrase)  ; 4-word passphrase
(forge 'german 'passphrase 6) ; 6-word German passphrase")
      (p "Each word reports its entropy. Passphrases join words with hyphens. The forge is an easter egg - undocumented in help, discovered by schemers exploring the REPL."))

    (subsection
      "7.6 Cryptographic Entropy"
      (p "Passwords fall naturally out of pronounceable words when the entropy source is sound. Forge uses /dev/urandom for cryptographically secure randomness, not pseudo-random generators.")
      (p "Boot-time verification runs automatically on module load:")
      (list
        (item "Confirms /dev/urandom exists and is readable")
        (item "Reads 256 test bytes and checks byte distribution")
        (item "Verifies no single byte appears more than ~10% (bias detection)")
        (item "Confirms at least 100 distinct byte values (diversity check)"))
      (p "If verification fails, the module refuses to load. An easter egg with real security - someone exploring the REPL discovers (forge) and gets actual cryptographic passwords, not toys."))

    (subsection
      "7.7 Audit Trail Heritage"
      (p "The cryptographic audit trail (Memo-0005) descends from VMS SECURITY.AUDIT$JOURNAL and the cluster-wide security infrastructure of VMS 6.0 (1993). That system introduced:")
      (list
        (item "SECURITYPOLICY bit 7 propagation")
        (item "Intrusion detection state replicated cluster-wide")
        (item "Breakin attempts detected across all nodes as one")
        (item "TLV-encoded object store")
        (item "The [000000]SECURITY.SYS file in ODS5 stored SECURITYCLASS records"))
      (p "The design principle then, as now: cluster nodes behave identically. N nodes, one security domain. Every significant action audited, every audit record signed.")
      (p "Cyberspace audit trails apply the same principle at IPv6 scale.")))

  (section
    "8. The Novice Interface"
    (p "Cyberspace must be approachable by normal people. The terminal is for operators. A friendly interface layer serves everyone else.")

    (subsection
      "8.1 The Problem"
      (p "A novice asked: \"Why would I want to use this? I have iCloud. They have recipes and cat pictures.\"")
      (p "Valid question. The answer must be compelling without mentioning Ed25519, SPKI certificates, hash chains, Merkle trees, or S-expressions."))

    (subsection
      "8.2 What Novices Want"
      (p "They don't want a distributed cryptographic vault. They want:")
      (list
        (item "My stuff is mine - Not rented from a corporation")
        (item "It survives - No company shutdown deletes my photos")
        (item "I control sharing - Family, not platforms")
        (item "Privacy - My recipes aren't AI training data")
        (item "Legacy - Grandkids can inherit the vault")
        (item "No ads - I'm not the product")))

    (subsection
      "8.3 Two Doors"
      (code "                    CYBERSPACE
                        │
           ┌────────────┴────────────┐
           │                         │
     ┌─────▼─────┐             ┌─────▼─────┐
     │ Terminal  │             │ Friendly  │
     │   (cs)    │             │   Door    │
     └─────┬─────┘             └─────┬─────┘
           │                         │
       Operators                  Novices
        Hackers                   Family
        Admins                   Everyone")
      (p "The terminal offers full power and complexity for those who want it. The friendly door offers drag-and-drop simplicity - same operations, different presentation.")
      (p "Both doors lead to the same vault. Both use the same Scheme underneath."))

    (subsection
      "8.4 Principles"
      (list
        (item "Never dumb down the core - Scheme stays Scheme")
        (item "Add layers, don't subtract - Friendly is additional, not replacement")
        (item "Same operations - Both doors do the same things")
        (item "Gradual revelation - Novices can discover the terminal if curious")
        (item "Family friendly - Grandma can use it")))

    (subsection
      "8.5 The Test"
      (p "If a novice can create a vault in 30 seconds, add a photo in 5 seconds, invite family in 1 minute, and understand what they have - we've succeeded."))

    (subsection
      "8.6 The Koan"
      (p "There is no point scaling to 2^128 if you assume everyone is a Schemer.")
      (p "The cryptographic address space, the capability chains, the Merkle proofs — all of that is implementation. The user doesn't sign certificates, they approve a peer. They don't query the vault, they inspect soup.")
      (p "If the system requires understanding SPKI to use safely, the system failed. The security properties must emerge from natural actions, not careful ones.")
      (p "The complexity serves the simplicity, not the other way around.")))

  (section
    "9. Cryptographic Selections"
    (p "Every cryptographic algorithm in Cyberspace was chosen for specific properties. This section documents the selections and their rationale.")

    (subsection
      "9.1 Signatures"
      (table
        (header "Algorithm" "Use" "Selection Rationale")
        (row "Ed25519" "Primary signatures" "Small keys (32B), fast, constant-time, no RNG needed for signing")
        (row "SPHINCS+" "Post-quantum (planned)" "Hash-based, conservative security, stateless")
        (row "Dilithium" "Post-quantum (planned)" "Lattice-based, smaller signatures than SPHINCS+, NIST selected")
        (row "Lamport" "Reference implementation" "Educational, hash-only security, foundation for SPHINCS+"))
      (p "Ed25519 is the current standard. Post-quantum migration uses hybrid signatures (Ed25519 + SPHINCS+ or Dilithium) to preserve security if either scheme breaks."))

    (subsection
      "9.2 Hash Functions"
      (table
        (header "Algorithm" "Use" "Selection Rationale")
        (row "SHA-512" "Object identity, signatures" "Conservative choice, 256-bit quantum security")
        (row "BLAKE2b" "Content addressing, KDF" "Faster than SHA-2, proven design, libsodium native")
        (row "SHAKE256" "Post-quantum Merkle (planned)" "XOF for variable output, SHA-3 family, NIST standard")
        (row "Argon2id" "Passphrase stretching" "Memory-hard, resists GPU/ASIC, winner of PHC"))
      (p "Hash functions survive quantum computers. Shor's algorithm (exponential speedup) breaks signatures and key exchange but not hashes. Grover's algorithm provides only quadratic speedup against hashes — halving effective security bits, not destroying them.")
      (p "SHA-512's 512 bits become 256-bit quantum security. Still beyond brute force. SHA-256 would drop to 128-bit quantum security — acceptable but less margin. We chose SHA-512 for the conservative 256-bit post-quantum level.")
      (p "BLAKE2b (256-bit output) provides 128-bit quantum security, sufficient for content addressing where collision resistance matters more than preimage resistance."))

    (subsection
      "9.3 Symmetric Encryption"
      (table
        (header "Algorithm" "Use" "Selection Rationale")
        (row "XSalsa20-Poly1305" "Vault encryption" "NaCl default, 24-byte nonce, proven AEAD")
        (row "ChaCha20-Poly1305" "Object encryption" "IETF standard, 12-byte nonce, streaming")
        (row "XChaCha20-Poly1305" "Keystore" "Extended nonce (24B), random nonce safe"))
      (p "The Salsa20/ChaCha20 family was chosen over AES: no timing attacks, no hardware requirements, Poly1305 is provably secure MAC. The 'X' variants use extended nonces, safe for random generation."))

    (subsection
      "9.4 Key Exchange"
      (table
        (header "Algorithm" "Use" "Selection Rationale")
        (row "X25519" "Ephemeral key exchange" "Curve25519 ECDH, constant-time, small keys")
        (row "HKDF" "Key derivation" "RFC 5869, extract-then-expand, domain separation"))
      (p "X25519 provides forward secrecy for CIP channels. Session keys are derived via HKDF with protocol-specific info strings for domain separation."))

    (subsection
      "9.5 Secret Sharing"
      (table
        (header "Algorithm" "Use" "Selection Rationale")
        (row "Shamir SSS" "Key backup, threshold recovery" "Information-theoretic security, GF(2^8) arithmetic"))
      (p "Shamir's scheme splits secrets into n shares where any k can reconstruct. Used for master key backup (5-of-9) and threshold governance."))

    (subsection
      "9.6 Blind Signatures (Chaum)"
      (p "David Chaum's 1982 blind signature scheme enables anonymous credentials. The Library holds four Chaum papers:")
      (list
        (item "Blind Signatures for Untraceable Payments (1982) — the foundation")
        (item "Untraceable Electronic Cash (1988, with Fiat & Naor)")
        (item "Untraceable Electronic Mail (1981) — mix networks")
        (item "The Dining Cryptographers Problem (1988) — unconditional anonymity"))
      (p "Cyberspace uses Chaum-style blind signatures for bearer capabilities: prove authorization without revealing identity. The issuer signs a blinded credential; when unblinded and presented, the signature verifies but cannot be linked to issuance.")
      (p "This preserves the choice Bitcoin abandoned: registered capabilities when you need accountability, bearer capabilities when you need privacy."))

    (subsection
      "9.7 Merkle Trees"
      (p "Content authentication via binary hash trees. Current implementation uses SHA-512; post-quantum migration to SHAKE256 or BLAKE3.")
      (p "Properties: O(log n) inclusion proofs, streaming verification, append-only audit logs. Merkle's 1987 paper is in the Library."))

    (subsection
      "9.8 Random Number Generation"
      (p "All randomness flows through libsodium's randombytes_buf(), which uses:")
      (list
        (item "Linux: getrandom(2) syscall")
        (item "macOS: arc4random_buf()")
        (item "OpenBSD: arc4random_buf() (ChaCha20-based)"))
      (p "Hardware entropy (RDRAND/RDSEED) feeds the OS pool. Quantum RNG (ID Quantique, drand beacons) planned for Phase 3+."))

    (subsection
      "9.9 The TCB Principle"
      (p "The Trusted Computing Base holds only:")
      (list
        (item "Ed25519 sign/verify")
        (item "SHA-512 hash")
        (item "Certificate chain verification"))
      (p "Everything else is policy. The TCB is ~1000 lines of OCaml calling libsodium, proven in Coq, frozen. This minimizes the attack surface: prove the crypto, evolve the rest freely.")))

  (section
    "10. Release Gates"
    (p "Two formal verification milestones gate Cyberspace releases:")

    (subsection
      "10.1 Beta Gate: Coq Extraction"
      (p "The TCB must be machine-verified before beta. SpkiTcb.v defines the security model; extraction produces spki_tcb.ml. Hand-written code that 'matches the spec' is not verified — it's aspirational.")
      (p "The critical property: capability attenuation (tag_intersect only shrinks permissions). The Coq proofs establish this mathematically. Without verified extraction, the trust anchor is unverified.")
      (p "Beta ships when:")
      (list
        (item "All Admitted proofs in SpkiTcb.v are complete")
        (item "Coq extraction produces working OCaml")
        (item "Extracted code passes test_tcb.ml")))

    (subsection
      "10.2 Release Gate: TLA+ Specification"
      (p "Distributed protocols (gossip, federation, consensus) must be model-checked before release. TLA+ formalizes the state machines; TLC exhaustively explores state space.")
      (p "TLA+ is a trailing artifact — you model what you've built, then verify it handles edge cases. Writing TLA+ for a moving target wastes effort.")
      (p "Release ships when:")
      (list
        (item "Gossip protocol modeled and checked")
        (item "Federation convergence modeled and checked")
        (item "No safety violations in TLC model checker"))))

  (section
    "11. VMS Lineage"

    (subsection
      "11.1 VMS Security (1984-1994)"
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
      "11.2 The Road Not Taken"
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
      "11.3 Languages"
      (p "BLISS - Bill Wulf at CMU (1969) created BLISS as an expression language, not 'DEC's C'. Everything returns a value. Lisp in systems clothing.")
      (p "MACRO-32 - VAX assembly with rich macros. The kernel was MACRO-32. Learned it from the privilege auditing rototill.")
      (p "The VMS Runtime - Had a rich macro wrapper for BLISS. That macro system was a Lisp. We knew. That's why we used it.")
      (p "A Lisper who fell in love with BLISS (an expression language, like home)."))

    (subsection
      "11.4 System Service Vocabulary"
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
      "11.5 Syntax Heritage"
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
    "12. Interface Philosophy"

    (subsection
      "12.1 English on Top, Scheme Underneath"
      (code "Terminal:    English verbs for mortals
REPL:        Scheme for hackers
Commands:    Forever cast in English/Scheme
Messages:    Multilingual (the command line speaks your tongue)"))

    (subsection
      "12.2 For the Uninitiated"
      (code scheme "(about)      ; What is this place?
(huh?)       ; Same question, different inflection
(what?)      ; Still the same
(describe)   ; For the formal")
      (p "The answer morphs with the weave. Standing alone, it suggests enrollment. With peers, it lists them. The description reflects the current state--not a static brochure but a living mirror of the constellation."))

    (subsection
      "12.3 Workstations and Terminals"
      (p "Workstations and terminals weren't wrong. PCs aren't the answer to everything. The right interface for the job at hand. Sometimes your native language is superior.")
      (p "Cyberspace runs on terminals because that's what operators use."))

    (subsection
      "12.4 The Period as Imperative (Smalltalk Heritage)"
      (p "In Smalltalk, the period terminates a statement. It's the moment of commitment--everything before it is preparation, the period makes it so.")
      (p "Cyberspace borrows this: any command suffixed with '.' implies execution and propagation. 'commit.' means commit and sync. 'fix.' means fix and make it so.")
      (code "commit    → stage the intention
commit.   → stage, execute, propagate to the weave")
      (p "The period is not punctuation. It's the imperative mood. Smalltalk understood that the moment of action deserves its own syntax."))

    (subsection
      "12.5 Do All the Th[i,a]nga"
      (p "The full toolchain invocation: commit, push, regen-all, publish. An idea isn't complete until it's self-contained and self-documenting in the weave.")
      (code "thinga := commit → push → regen-all → publish")
      (p "regen-all is the totality of sanity checking before publishing: recompile all modules, verify types, run tests, regenerate documentation. Nothing reaches the weave without passing the scrutinizer--a nod to Felix Winkelmann's CHICKEN Scheme, whose scrutinizer catches what the programmer misses. It has more inference because it's in lambda.")
      (p "The spelling nods to both 'things' and 'thanga' (Tamil: gold). Ideas forged through the full cycle become permanent--golden artifacts in the weave.")
      (p "Partial work stays local. Published work is proven. The toolchain is the crucible.")))

  (section
    "13. The Soup"
    (p "The vault browser is called 'soup' after Newton's persistent object store (1993).")
    (code "Newton soup:      Persistent frames, automatic storage
Cyberspace soup:  Vault objects, content-addressed")
    (p "Apple Newton -> Dylan -> Scheme. The soup survives.")
    (code scheme "(soup)              ; browse the vault
(soup 'keys)        ; list keys
(soup-stat 'alice)  ; inspect object"))

  (section
    "14. The Raga Favicon"
    (p "The Library's favicon is a lambda whose color morphs through the day.")

    (subsection
      "14.1 The Prahar (Watches)"
      (code "04-06  violet    brahma muhurta (pre-dawn meditation)
06-08  gold      dawn
08-11  teal      morning
11-14  phosphor  midday
14-17  neon      afternoon
17-19  orange    sunset
19-22  coral     evening
22-04  cyan      night"))

    (subsection
      "14.2 Why Ragas?"
      (p "Indian classical music assigns ragas to specific times of day. A morning raga played at midnight is wrong--not because of rules, but because it doesn't fit. The music knows when it should be heard."))

    (subsection
      "14.3 Why a Breathing Lambda?"
      (p "The lambda isn't just a logo--it's the fundamental unit. What Scheme computes, what the weave is made of. Every function, every object, every sealed thing in the vault is lambdas all the way down.")
      (p "The color morphing isn't decoration--it's the weave breathing. Lambdas are being gathered, tested, frozen into vaults across time zones. The color you see is the pulse of that activity. Dawn gold as the eastern hemisphere wakes and contributes. Phosphor green at peak hours. Cyan in the quiet night when the squirrels rest."))

    (subsection
      "14.4 The Easter Egg"
      (p "Someone notices their lambda is orange, asks why, and learns: 'You're seeing sunset. Somewhere, lambdas are being gathered into the weave of Cyberspace.'")
      (p "Those who need to ask are in need of enlightenment. The Library is here to provide it. They came for the RFCs, they left understanding the lambda.")
      (p "The brahma muhurta violet isn't just pretty--it's the hour of enlightenment. If they're seeing violet, they're already up at the right time.")))

  (section
    "15. Little Fluffy Clouds"
    (p "'What were the skies like when you were young?' -- The Orb, 1990")
    (p "The realms in the weave are clouds--little fluffy clouds drifting in ambient space. The Orb understood distributed systems before we had the words: layers of sound, samples from elsewhere, everything floating, nothing anchored to a single point.")
    (p "Fluffy leads the weave. The name was never arbitrary.")
    (p "The skies when we were young were phosphor green, VT100s in machine rooms, the hum of VAXen. Now the clouds are realms, and the realms are lambdas, and the lambdas float in the wilderness of mirrors.")
    (p "Ambient for the ages. Distributed for the future."))

  (section
    "16. Derivation vs. Discovery"

    (subsection
      "16.1 Lamport Time"
      (p "In the absence of global clock synchronization, distributed systems establish causal ordering through logical clocks (Lamport, 1978). Each node maintains a local counter incremented on message send/receive, establishing a happens-before relation that provides partial ordering without requiring synchronized wall-clock time.")
      (p "The happens-before relation was always there--Lamport gave it a name and a notation. That's discovery. Seeing what was already true."))

    (subsection
      "16.2 call/cc"
      (p "Most language features are about what you can say. call/cc is about what exists.")
      (p "call/cc says: the future of the computation is a value you can hold, store, invoke later. Continuations. Time as a first-class object. That's not syntax preference--that's ontology.")
      (p "The continuation exists whether you capture it or not--call/cc just lets you name it. The future was always there, implicit in every expression. Scheme made it explicit.")
      (p "SICP wasn't about parentheses. It was a course in thinking, disguised as a programming textbook. Streams, lazy evaluation, the environment model, the metacircular evaluator--and then call/cc, which breaks your brain the right way."))

    (subsection
      "16.3 The Y Combinator"
      (p "The Y combinator (Y = λf.(λx.f(x x))(λx.f(x x))) is a fixed-point combinator enabling recursion without explicit self-reference. It's elegant. It's also just math that falls out of lambda calculus--derivation, not discovery.")
      (p "A certain Silicon Valley venture capital firm took the name as borrowed plumage. Value signaling to people who recognize the symbol but don't work in the calculus. The firm's founder wrote 'On Lisp', evangelized the aesthetic--but Arc didn't have call/cc. Common Lisp doesn't have it. He came from the CL side, where continuations aren't primitive.")
      (p "Naming the firm 'Y Combinator' signals: I read the cool parts. Not naming it 'call/cc' signals: I stopped before it got weird.")
      (p "The Y combinator is page 300 of SICP. call/cc is the last chapter. Most people don't finish."))

    (subsection
      "16.4 The Distinction"
      (p "Derivation: The Y combinator. Recursion falling out of self-application. True but not illuminating.")
      (p "Discovery: Lamport clocks. call/cc. Seeing structure that was always there, giving it a name, making it usable.")
      (p "Cyberspace is built on discoveries: happens-before for distributed time, continuations for control flow, SPKI for authorization. The derivations are implementation details."))

    (subsection
      "16.5 Why We Don't Use It"
      (p "Search the Cyberspace codebase for call/cc. You'll find it only in SRFI libraries (srfi-1, srfi-18) - never in application code.")
      (p "This is deliberate. Understand the deep machinery, use the simple tool:")
      (list
        (item "Exceptions → guard, handle-exceptions (srfi-34)")
        (item "Generators → srfi-158 (coroutine-like without full continuations)")
        (item "Early exit → explicit returns, not escape continuations")
        (item "Backtracking → explicit state, not captured futures"))
      (p "Captured continuations create implicit control flow. Every call/cc is a potential goto to anywhere the continuation was captured. In a security-critical codebase, implicit is the enemy.")
      (p "The condition system covers what most people use call/cc for. The rest is showing off.")
      (p "Appreciate the ontology. Deploy the mundane.")))

  (section
    "17. Timeline"
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
    (p "The Lisper finally gets to write Lisp."))

  (section
    "Changelog"
    (p "- 2026-01-22 — Folded designer-notes.scm into memo (open kimono); added call/cc rationale")
    (p "- 2026-01-21 — Added Release Gates (section 10): Coq for beta, TLA+ for release")
    (p "- 2026-01-19 — Added Audit Trail Heritage (section 7.7), moved from Memo-0005")
    (p "- 2026-01-18 — Expanded Why Scheme with homoiconicity rationale (section 1.2)")
    (p "- 2026-01-18 — Added The Koan (section 8.6): complexity serves simplicity")
    (p "- 2026-01-17 — Added Cryptographic Selections section (section 9)")
    (p "- 2026-01-17 — Corrected heritage: SDSI/Rivest, SPKI/Ellison, IETF merger (section 1.1)")
    (p "- 2026-01-17 — Added Novice Interface section (section 8)")
    (p "- 2026-01-15 — Gasser Multics provenance added (section 7.1)")
    (p "- 2026-01-15 — OSS operational geography framing, 40+ languages (section 7.3)")
    (p "- 2026-01-15 — Added cryptographic RNG with boot-time verification (section 7.6)")
    (p "- 2026-01-15 — Added forge/smelter heritage (section 7)")
    (p "- 2026-01-15 — Initial draft, heritage notes")))
