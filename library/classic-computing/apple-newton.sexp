;; Apple Newton Deep Dive Research
;; Compiled 2026-01-09

(research
  (title "Apple Newton MessagePad")
  (date "2026-01-09")
  (category classic-computing)

  (overview
    (manufacturer "Apple Computer")
    (launch-date "1993-08-03")
    (end-date "1998-02-27" "Steve Jobs canceled the project")
    (description "Personal digital assistant, pioneering ARM-based mobile device")
    (significance "First Apple product to use ARM processor"))

  (hardware-evolution
    (messagepad-original
      (year 1993)
      (processor "ARM 610" "20 MHz")
      (ram "640 KB")
      (rom "4 MB")
      (display "336x240 pixels" "monochrome"))

    (messagepad-2000
      (year 1997)
      (processor "StrongARM SA-110" "162 MHz" "8x faster than ARM 610")
      (flash "4 MB")
      (display "480x320 pixels" "grayscale")
      (backlight "yes"))

    (emate-300
      (year 1997)
      (processor "ARM 710a" "25 MHz")
      (form-factor "Clamshell with keyboard")
      (target "Education market")))

  (operating-system
    (name "Newton OS")
    (layers
      (microkernel "Task and memory management")
      (system "C++ - communications, handwriting recognition, NewtonScript VM")
      (applications "NewtonScript - built-in and user apps")))

  (newtonscript
    (designer "Walter Smith")
    (paradigm "Prototype-based object-oriented")
    (influences "Self" "Smalltalk")
    (predecessor "Dylan was original choice, not ready in time")

    (memory-efficiency
      "Prototype inheritance allowed GUI objects to reference ROM
       prototypes directly, saving precious RAM. Only _proto and
       _parent fields needed instead of full object copies.")

    (development-tools
      (ntk "Newton Toolkit" "$1000" "Mac OS and Windows")
      (newt-0 "NEWT/0" "2003" "Makoto Nukui" "Cross-platform interpreter")))

  (dylan-connection
    (codename "Ralph" "after Ralph Ellison, Invisible Man author")
    (team "Apple Advanced Technology Group")
    (goal "Combine best of Smalltalk, Lisp, and C++")
    (outcome "Too late for Newton, retargeted to general computing")

    (primary-designers
      "Glenn S. Burke"
      "Robert Cassels"
      "John Hotchkiss"
      "Jeremy A. Jones"
      "David A. Moon"
      "Jeffrey Piazza"
      "Andrew Shalit"
      "Oliver Steele"
      "Gail Zacharias")

    (reference-manual-authors
      "Andrew Shalit"
      "David A. Moon"
      "Orca Starbuck")

    (heritage
      "Derives from Scheme and Common Lisp"
      "Object system from CLOS"
      "Created by team responsible for Macintosh Common Lisp")

    (modern-implementations
      (gwydion-dylan "Dylan-to-C compiler")
      (open-dylan "Native code for Intel" "https://opendylan.org/")))

  (david-moon
    (description "Programmer and computer scientist")
    (contributions
      (maclisp "Reimplemented Maclisp on Multics at MIT")
      (emacs "Co-creator with Guy L. Steele Jr. of original TECO Emacs")
      (symbolics "Founder, 1980. Symbolics Fellow 1989.")
      (common-lisp "Major contributor to standardization")
      (dylan "Primary language designer at Apple")
      (ephemeral-gc "Inventor of ephemeral garbage collection")
      (plot "Programming Language for Old Timers, 2006"))

    (steele-gabriel-quote
      "A seductively powerful thinker, quiet and often insulting,
       whose arguments are almost impossible to refute."))

  (rom-images
    (source "https://archive.org/download/AppleNewtonROMs")
    (files
      ("MessagePad OMP v1.00.rom" "4 MB")
      ("MessagePad OMP v1.3.rom" "4 MB")
      ("MessagePad 110 v1.2.rom" "4 MB")
      ("MessagePad 120 v1.3 (444217).rom" "4 MB")
      ("MessagePad 130 v2.x (525314).rom" "8 MB")
      ("MessagePad 2000 (717006).rom" "8 MB")
      ("MessagePad 2100 (717006).rom" "8 MB")
      ("eMate 300 (717006).rom" "8 MB")
      ("Sharp ExpertPad PI-7000 v1.10.rom" "4 MB")
      ("Motorola Marco v1.3 (444347).rom" "4 MB")
      ("Siemens NotePhone v1.1.rom" "4 MB")
      ("Notepad v1.0b1.rom" "4 MB")
      ("Newt J1Armistice image" "4 MB")
      ("Lindy 803AS.00 (2.0a6).rom" "16 MB")))

  (emulation
    (einstein
      (description "Newton emulator")
      (rom-dumping "Built-in ROM dumper via network")
      (wiki "https://github.com/pguyot/Einstein/wiki/Dumping-The-Rom")))

  (legacy
    (capabilities-still-unique
      "Extend existing apps seamlessly"
      "Handwriting recognition (final version was excellent)")

    (arm-influence
      "Larry Tesler identified need for advanced low-power processor"
      "Led to partnership with Acorn to create ARM Ltd."))

  (resources
    (newton-faq "http://newtonfaq.com/")
    (newtonscript-org "http://newtonscript.org/")
    (unna "http://www.unna.org/" "United Network of Newton Archives")
    (apple-archives "http://www.applearchives.com/newton/")
    (internet-archive "https://archive.org/details/newton-museum")
    (thomas-tempelmann "https://www.tempel.org/newton/")))
