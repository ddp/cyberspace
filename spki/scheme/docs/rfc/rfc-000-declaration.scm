;; RFC-000: Declaration of the Library of Cyberspace
;; Source format: S-expression document

(rfc
  (number 000)
  (title "Declaration of the Library of Cyberspace")
  (status proposed)
  (date "January 2026")
  (author "Derrell Piper" "ddp@eludom.net")

  (abstract
    (p "This document declares the founding principles of the Library
        of Cyberspace: a federated, cryptographically-secured system
        for preserving and sharing human knowledge without central
        authority."))

  (section "Preamble"
    (blockquote "E Pluribus Unum" (cite "Out of many, one."))

    (p "We hold these truths to be self-evident in the digital age:")

    (list
      (item "Knowledge belongs to humanity, not corporations")
      (item "Preservation requires distribution")
      (item "Trust requires cryptography, not authority")
      (item "Access requires federation, not permission")))

  (section "Principles"

    (subsection "No Central Authority"
      (p "The Library has no master server, no root certificate authority,
          no single point of control or failure. Each node is sovereign.
          Trust flows from cryptographic proof, not institutional blessing.")

      (diagram
        (row (box "Alice") (arrow "<--->") (box "Bob") (arrow "<--->") (box "Carol"))
        (row (spacer) (box "No Central Authority" :style emphasis) (spacer))
        (row (spacer) (text "Just keys, seals, trust") (spacer))))

    (subsection "Cryptographic Foundation"
      (p "Every artifact is sealed with its creator's signature.
          Every action is logged in tamper-evident audit trails.
          Every delegation is expressed in SPKI certificates.")

      (list
        (item (term "Signatures") "Ed25519 for authenticity")
        (item (term "Hashes") "SHA-512 for integrity")
        (item (term "Certificates") "SPKI for authorization")))

    (subsection "Federated Preservation"
      (p "No single library burns. Knowledge replicates across nodes
          through gossip protocols. Consensus emerges from quorum,
          not decree.")))

  (section "Architecture"
    (p "The Library comprises:")

    (table
      (header "Component" "Purpose" "RFC")
      (row "Vault" "Content-addressed storage" "RFC-006")
      (row "Audit Trail" "Tamper-evident logging" "RFC-003")
      (row "SPKI Certificates" "Authorization without identity" "RFC-004")
      (row "Federation" "Peer-to-peer synchronization" "RFC-010")
      (row "Threshold Governance" "Multi-party authorization" "RFC-007")))

  (section "Inspiration"
    (p "Built on 50 years of cryptographic research:")

    (references
      (ref "Diffie & Hellman" 1976 "New Directions in Cryptography")
      (ref "Lamport" 1978 "Time, Clocks, and the Ordering of Events")
      (ref "Shamir" 1979 "How to Share a Secret")
      (ref "Merkle" 1987 "Digital Signatures Based on Conventional Encryption")
      (ref "Haber & Stornetta" 1991 "How to Time-Stamp a Digital Document")
      (ref "Ellison et al." 1999 "SPKI Certificate Theory")))

  (section "Commitment"
    (blockquote
      "The Library of Cyberspace stands as a testament to what
       free people can build when they trust mathematics over
       institutions, distribution over centralization, and
       each other over authorities."))

  (footer
    (p "This declaration is sealed in the vault, replicated across
        the federation, and preserved for posterity.")
    (sig "Derrell Piper" "January 2026")))
