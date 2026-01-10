;; Classic Mac OS History
;; Compiled 2026-01-09

(research
  (title "Classic Mac OS: System Software to Mac OS 9")
  (date "2026-01-09")
  (category classic-computing)

  (overview
    (span "1984-2001")
    (versions "System 1.0 to Mac OS 9.2.2")
    (architecture "Single-user, single-tasking evolved to cooperative multitasking")
    (limitations
      "All applications share one memory space"
      "No memory protection"
      "Cooperative multitasking only"))

  (resource-fork
    (description "Unique Mac OS feature: files have two forks")
    (data-fork "Raw data, like other operating systems")
    (resource-fork "Structured data: icons, menus, dialogs, code")
    (significance "Enabled easy localization and customization"))

  (resedit
    (name "ResEdit" "Resource Editor")
    (type "Developer tool and power user utility")
    (history
      (prototype "Rony Sebok and Steve Capps, Cupertino")
      (completion "Gene Pope of Apple")
      (first-release "March 1985, version 1.0")
      (distribution "Software Supplement, May/July 1985"))
    (final-version "2.1.3" "August 1994")
    (features
      "GUI layout tool - revolutionary for mid-1980s"
      "Edit window templates (WIND)"
      "Edit menus (MENU)"
      "Edit dialog boxes"
      "Edit controls (CNTL)"
      "Edit color palettes (clut, pltt)"
      "Edit icons (ICON, cicn, ICN#)")
    (legacy
      "Never updated for PowerPC native"
      "Never updated for Mac OS X"
      "Runs in Classic mode or emulators (SheepShaver, Basilisk II)")
    (alternatives
      (resorcerer "Commercial, still available")
      (resknife "Open source Mac OS X native")
      (resforge "Open source, modern macOS"
                "https://github.com/andrews05/ResForge"
                "MIT License, Apple Silicon native"))
    (download
      (macintosh-garden "https://macintoshgarden.org/apps/resedit")
      (macintosh-repository "https://www.macintoshrepository.org/1317-resedit-2-1-x"))
    (reference-manual "https://developer.apple.com/library/archive/documentation/mac/pdf/ResEditReference.pdf"))

  (copland
    (codename "Copland" "after Aaron Copland, American composer")
    (development "1994-1996")
    (intended-name "System 8" "later Mac OS 8")
    (status "Never commercially released")
    (cancellation "August 1996, announced by CTO Ellen Hancock")

    (goals
      "Protected memory"
      "Preemptive multitasking"
      "Retain compatibility with existing Mac applications")

    (architecture
      (microkernel "NuKernel"
        (based-on "Mach 3.0 concepts")
        (features
          "Preemptive multitasking"
          "Synchronization primitives"
          "Large sparse address spaces"
          "Memory-mapped files"
          "Demand-paged virtual memory"
          "Soft real-time scheduling for multimedia"))

      (design "Microkernel with multiple servers")
      (servers
        "Networking - separate process"
        "File services - separate process"
        "Display management - separate process")
      (blue-box
        (official-name "Cooperative Macintosh Toolbox environment")
        (description "System 7 encapsulated in single process")
        (failure-mode "Crash takes down blue box only, auto-restarts")))

    (reasons-for-failure
      (feature-creep "Continuous addition of features beyond original scope")
      (empire-building "Internal politics, fragmented teams, silos")
      (impossible-constraint "Add modern plumbing while maintaining compatibility")
      (timeline "Could not be done in two years")
      (stability "Leaked betas crashed even when idle"))

    (aftermath
      (decision "Look outside Apple for new OS")
      (acquisition "NeXTSTEP purchased 1997")
      (result "NeXTSTEP became Mac OS X")
      (legacy "XNU kernel realized Copland's goals via different path"))

    (historical-note
      "PCWorld 2008: One of biggest project failures in IT history"))

  (mac-os-9
    (release-date "1999-10-23")
    (marketing "The Best Internet Operating System Ever")
    (features
      "Sherlock 2 Internet search"
      "iTools integration"
      "Improved Open Transport networking")

    (mac-os-9-2-2
      (release-date "2001-12-05")
      (significance "Final release of classic Mac OS")
      (purpose "Bug fixes for Classic environment in Mac OS X")
      (no-new-features #t)
      (compatibility "Mac OS X 10.1 through 10.4.11 Classic mode"))

    (end-of-development
      (date "Late 2001")
      (announcement "WWDC May 2002, San Jose")
      (ceremony "Steve Jobs mock funeral with coffin")
      (last-macs-with-os9
        "Power Mac G4 Mirrored Drive Doors rerelease, June 2003")
      (g5-support "None - Mac OS 9 only supports G3 and G4"))

    (transition-to-os-x
      (classic-environment "Compatibility layer in Mac OS X 10.0-10.4")
      (purpose "Run Mac OS 9 applications in emulation")
      (removal "Not available on Intel Macs or Mac OS X 10.5+")))

  (resources
    (resedit-download "https://macintoshgarden.org/apps/resedit")
    (resforge "https://github.com/andrews05/ResForge")
    (copland-archive "https://archiveos.org/copland/")
    (eclectic-light "https://eclecticlight.co/" "Excellent Mac history articles")))
