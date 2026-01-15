;; Memo-0000: Declaration of Cyberspace
;; The founding document of the Library of Cyberspace

(memo
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
    (p "This is the shape that systems take when they are allowed to find their natural form. Plan 9 found it in files. Lisp found it in S-expressions. Simple Public Key Infrastructure (SPKI) found it in capabilities. We find it in the soup.")
    (p "The language is incidental. The shape is inevitable."))

  (section
    "The Ten Specifications"
    (table
      (header "No." "Title" "Principle")
      (row "I" "Replication Layer" "Distribution without permission")
      (row "II" "Architecture" "Separation of mechanism and policy")
      (row "III" "Audit Trail" "Accountability through transparency")
      (row "IV" "Public Key Authorization" "Authority without identity")
      (row "V" "Metadata Levels" "Progressive disclosure")
      (row "VI" "Vault Architecture" "Sealed truth")
      (row "VII" "Threshold Governance" "Democracy in code")
      (row "VIII" "Shamir Sharing" "Trust through distribution")
      (row "IX" "Library Directory" "Knowledge freely accessible")
      (row "X" "Federation" "Union without empire")))

  (section
    "License"
    (p "The Library of Cyberspace is released under the MIT License:")
    (code "Copyright (c) Derrell Piper

Permission is hereby granted, free of charge, to any person
obtaining a copy of this software and associated documentation
files (the \"Software\"), to deal in the Software without
restriction, including without limitation the rights to use,
copy, modify, merge, publish, distribute, sublicense, and/or
sell copies of the Software, and to permit persons to whom the
Software is furnished to do so, subject to the following
conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED \"AS IS\", WITHOUT WARRANTY OF ANY KIND.")
    (p "No GNU. No GPL. No copyleft. Mathematics belongs to everyone."))

  (section
    "Acknowledgments"
    (p "This declaration stands on the shoulders of giants:")
    (list
      (item "The Grateful Dead, who understood that sharing creates more value than hoarding, and whose tape-trading gift economy prefigured the commons")
      (item "John Perry Barlow, Dead lyricist and cyberspace prophet, whose 1996 Declaration of Independence lit the way")
      (item "Thomas Jefferson, who wrote the declaration of human liberty in language that still echoes")
      (item "Alexander Hamilton, who designed federation—sovereignty with union—in the Federalist Papers")
      (item "Hal Abelson and Gerald Jay Sussman, who showed in Structure and Interpretation of Computer Programs that from a few primitives, you can build everything"))
    (p "The language is incidental. The shape is inevitable."))

  (footer
    (p "E Pluribus Unum")
    (p "Signed under cryptographic seal:")
    (code "@ddp+{sign,delegate}:/declarations/cyberspace/000
  realm:      Starlight
  principal:  ed25519:7f83b1657ff1fc53b92dc18148a1d65dfc2d4b1fa3d677284addd200126d9069
  email:      ddp@eludom.net (Memo-822 binding)
  node:       Darwin-arm64 (Apple M4, 10 cores, 32GB)
  federation: Sovereign
  timestamp:  2026-01-06T00:00:00Z
  witness:    threshold(2,3) via Memo-0008
  seal:       BLAKE2b-256")
    (p "The principal coordinates identify the signer in cyberspace. The +{sign,delegate} capabilities authorize this document and permit others to co-sign. The realm is the local sovereign domain. The federation is the trust boundary. The witness quorum ensures no single point of authority. The seal binds intent to mathematics.")
    (link "https://www.yoyodyne.com/ddp/cyberspace/spki/scheme/docs/notes/index.html" "Enter the Library")))
