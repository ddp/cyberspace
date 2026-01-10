;; Classic Computing Library Index
;; Compiled 2026-01-09

(library-section
  (name "classic-computing")
  (description "Historical computing platforms, source code archives, and preservation")
  (created "2026-01-09")

  (contents
    (sol-20-electric-pencil
      (file "sol-20-electric-pencil.sexp")
      (topics
        "Processor Technology Sol-20"
        "VDM-1 display and character generator"
        "Electric Pencil word processor"
        "Helios II disk system"
        "Personality modules and SOLOS"))

    (apple-newton
      (file "apple-newton.sexp")
      (topics
        "Newton MessagePad hardware evolution"
        "Newton OS architecture"
        "NewtonScript programming language"
        "Dylan programming language history"
        "David Moon - Lisp, Symbolics, Dylan"
        "ARM processor origins"
        "ROM images and emulation"))

    (apple-lisa
      (file "apple-lisa.sexp")
      (topics
        "Lisa hardware and architecture"
        "Lisa OS source code release (CHM 2023)"
        "Relationship to Macintosh"
        "LisaEm emulation"))

    (apple-macintosh
      (file "apple-macintosh.sexp")
      (topics
        "Macintosh 128K hardware"
        "Burrell Smith's design philosophy"
        "Andy Hertzfeld's system software"
        "Bill Atkinson's QuickDraw and MacPaint"
        "Source code releases"))

    (classic-mac-os
      (file "classic-mac-os.sexp")
      (topics
        "Resource fork architecture"
        "ResEdit - resource editor"
        "Copland and NuKernel"
        "Mac OS 9.2.2 - final classic release"
        "Steve Jobs mock funeral for OS 9"
        "Transition to Mac OS X"))

    (macintosh-common-lisp
      (file "macintosh-common-lisp.sexp")
      (topics
        "Coral Common Lisp origins"
        "Apple Cambridge ATG campus"
        "MCL to Clozure CL lineage"
        "SK8 and Apple Dylan"
        "Gary Byers, Jeremy Jones, Andrew Shalit"))

    (apl-history
      (file "apl-history.sexp")
      (topics
        "APL\\360 and APL/SV"
        "IBM source code release"
        "Computer History Museum Art of Code series"))

    (dec-prism-mica
      (file "dec-prism-mica.sexp")
      (topics
        "PRISM architecture (1982-1988)"
        "MICA multipersonality OS"
        "Emerald VMS port"
        "Dave Cutler career"
        "Epicode to PALcode evolution"
        "Alpha origins"
        "Windows NT influence")))

  (key-resources
    (computer-history-museum "https://computerhistory.org/")
    (internet-archive "https://archive.org/")
    (sol20-org "https://www.sol20.org/")
    (open-dylan "https://opendylan.org/")
    (clozure-cl "https://ccl.clozure.com/")
    (macintosh-garden "https://macintoshgarden.org/")
    (eclectic-light "https://eclecticlight.co/"))

  (lineages
    (coral-to-clozure
      "Coral Software (1984)"
      "-> Apple acquisition (1988)"
      "-> Apple Cambridge ATG"
      "-> Digitool (1994)"
      "-> Clozure Associates"
      "Product: Coral CL -> MCL -> OpenMCL -> Clozure CL")

    (classic-to-osx
      "System 1.0 (1984)"
      "-> System 7 (1991)"
      "-> Copland attempt (1994-1996, failed)"
      "-> Mac OS 8/9 (1997-2001)"
      "-> NeXT acquisition (1997)"
      "-> Mac OS X (2001)")

    (prism-to-nt
      "SAFE/HR-32/CASCADE (1982-1984)"
      "-> PRISM unified (1985)"
      "-> MICA OS design"
      "-> Canceled (July 1988)"
      "-> Cutler to Microsoft (Oct 1988)"
      "-> Windows NT (1993)")

    (prism-to-alpha
      "PRISM (1985-1988)"
      "-> Canceled but silicon working"
      "-> Alpha project (1989)"
      "-> DECchip 21064 (1992)"
      "-> 'AXP = Almost eXactly PRISM'"))

  (future-additions
    "Xerox Alto and Smalltalk"
    "Symbolics Lisp Machines"
    "Sun Microsystems"
    "NeXT Computer"
    "Commodore Amiga"
    "Atari ST"
    "BeOS"
    "DEC VAX/VMS deep dive"
    "RSX-11 and PDP-11"))
