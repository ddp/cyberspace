;; Macintosh Common Lisp and Apple Cambridge
;; Compiled 2026-01-09

(research
  (title "Macintosh Common Lisp and Apple Cambridge")
  (date "2026-01-09")
  (category classic-computing)

  (overview
    (name "Macintosh Common Lisp" "MCL")
    (description "Common Lisp implementation and IDE for Macintosh")
    (platforms "Classic Mac OS (m68k, PPC)" "Mac OS X")
    (significance "Foundation for SK8 and Apple Dylan"))

  (history
    (development-start "1984")
    (original-name "Coral Common Lisp")
    (company "Coral Software")

    (apple-acquisition
      (date "Late 1988")
      (result "Renamed to Macintosh Common Lisp")
      (team-became "Apple Cambridge" "Cambridge campus of ATG"))

    (apple-cambridge
      (description "Advanced Technology Group campus")
      (origin "Coral Software acquisition")
      (director "Ike Nassi")
      (location "Cambridge, Massachusetts")
      (disbanded "1995")

      (key-people
        "Gary Byers"
        "Jeremy Jones"
        "Andrew Shalit"
        "Bill St. Clair"
        "Gail Zacharias")

      (projects
        (mcl "Continued MCL development for ~10 years")
        (sk8 "Multimedia authoring environment")
        (apple-dylan "Dylan implementation, initially for Newton")))

    (transfer-to-digitool
      (date "1994")
      (reason "PowerPC transition")
      (company "Digitool"))

    (atg-closure
      (date "1997")
      (result "Digitool acquired MCL completely"))

    (version-history
      (version-5 "2003" "First OS X native (Carbon) for PowerPC")
      (version-5-1 "2005" "Last commercial version")
      (version-5-2 "2007" "Open sourced")
      (rmcl "2009" "Based on 5.1, runs under Rosetta on Intel")))

  (technical-features
    (toolbox-integration
      "Famous for deep Macintosh Toolbox integration"
      "Direct access to Mac OS functionality from Lisp"
      "Low-level interface for native data structures"
      "High-level convenience interface"))

  (dylan-connection
    (relationship "Apple Dylan core implemented in MCL")
    (team-overlap "Dylan team overlapped with MCL team")
    (location "Both primarily at Cambridge campus")
    (architecture "MCL foundation, rest in Dylan"))

  (clozure-lineage
    (fork-date "1998")
    (original-name "OpenMCL")
    (reason-for-rename "MCL open sourced, avoid confusion")
    (current-name "Clozure CL" "CCL")
    (acronym-history "CCL originally meant Coral Common Lisp")

    (clozure-cl
      (description "Fast, mature, open source Common Lisp")
      (platforms "Linux" "Mac OS X" "FreeBSD" "Windows")
      (architectures "32-bit x86" "64-bit x86")
      (license "LGPL variant")
      (website "https://ccl.clozure.com/")
      (company "Clozure Associates"
               "Many same people as Coral, Apple Cambridge, Digitool"))

    (continuity
      "Coral Software -> Apple Cambridge -> Digitool -> Clozure Associates"
      "Coral Common Lisp -> MCL -> OpenMCL -> Clozure CL"))

  (resources
    (clozure-cl "https://ccl.clozure.com/")
    (clozure-history "https://ccl.clozure.com/history.html")
    (open-dylan-cambridge "https://opendylan.org/history/apple-dylan/apple-cambridge.html")
    (mactech-mcl "http://preserve.mactech.com/articles/mactech/Vol.09/09.01/MCL/index.html")))
