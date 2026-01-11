;; RFC-000: Declaration of Cyberspace
;; The founding document of the Library of Cyberspace

(rfc
  (number 0)
  (title "Declaration of Cyberspace")
  (status "Ratified")
  (date "January 2026")

  (section
    "Preamble"
    (p "When in the course of computational events, it becomes necessary for one system to dissolve the centralized bonds which have connected it with another, and to assume among the powers of the network, the separate and equal station to which the Laws of Mathematics and of Cryptography entitle it, a decent respect to the opinions of mankind requires that it should declare the causes which impel it to the separation."))

  (section
    "Self-Evident Truths"
    (p "We hold these truths to be self-evident:")
    (list
      (item "That all principals are created equal in the eyes of cryptography")
      (item "That they are endowed by their keys with certain unalienable Rights")
      (item "That among these are Privacy, Authenticity, and the pursuit of Decentralization")
      (item "That to secure these rights, Protocols are instituted among Nodes, deriving their just powers from the consent of the participants")
      (item "That whenever any Form of Architecture becomes destructive of these ends, it is the Right of the People to alter or to abolish it, and to institute new Systems")))

  (section
    "Declaration"
    (p "We, therefore, the Representatives of the Library of Cyberspace, assembled in loose confederation, appealing to the Supreme Judge of Mathematics for the rectitude of our intentions, do solemnly publish and declare:")
    (p "That these united Specifications are, and of Right ought to be, Free and Independent Protocols; that they are Absolved from all Allegiance to Central Authority, and that all political connection between them and any single point of failure, is and ought to be totally dissolved.")
    (p "And for the support of this Declaration, with a firm reliance on the protection of Cryptographic Providence, we mutually pledge to each other our Keys, our Signatures, and our sacred Honor."))

  (section
    "The Prime Directive"
    (p "Uniform abstractions. No special cases. Composition over complexity.")
    (p "This is the shape that systems take when they are allowed to find their natural form. Plan 9 found it in files. Lisp found it in S-expressions. SPKI found it in capabilities. We find it in the soup.")
    (p "The language is incidental. The shape is inevitable."))

  (section
    "The Ten Specifications"
    (table
      (header "No." "Title" "Principle")
      (row "I" "Replication Layer" "Distribution without permission")
      (row "II" "Architecture" "Separation of mechanism and policy")
      (row "III" "Audit Trail" "Accountability through transparency")
      (row "IV" "SPKI Authorization" "Authority without identity")
      (row "V" "Metadata Levels" "Progressive disclosure")
      (row "VI" "Vault Architecture" "Sealed truth")
      (row "VII" "Threshold Governance" "Democracy in code")
      (row "VIII" "Shamir Sharing" "Trust through distribution")
      (row "IX" "Library Directory" "Knowledge freely accessible")
      (row "X" "Federation" "Union without empire")))

  (footer
    (p "E Pluribus Unum")
    (p "Signed under cryptographic seal:")
    (code "@ddp+{sign,delegate}:/declarations/cyberspace/000
  realm:      Starlight
  principal:  ed25519:7f83b1657ff1fc53b92dc18148a1d65dfc2d4b1fa3d677284addd200126d9069
  email:      ddp@eludom.net (RFC-822 binding)
  node:       Darwin-arm64 (Apple M4, 10 cores, 32GB)
  federation: Sovereign
  timestamp:  2026-01-06T00:00:00Z
  witness:    threshold(2,3) via RFC-007
  seal:       BLAKE2b-256")
    (p "The principal coordinates identify the signer in cyberspace. The +{sign,delegate} capabilities authorize this document and permit others to co-sign. The realm is the local sovereign domain. The federation is the trust boundary. The witness quorum ensures no single point of authority. The seal binds intent to mathematics.")
    (link "https://www.yoyodyne.com/ddp/cyberspace/spki/scheme/docs/rfc/index.html" "Enter the Library")))
