;; Apple Macintosh Research
;; Compiled 2026-01-09

(research
  (title "Apple Macintosh 128K")
  (date "2026-01-09")
  (category classic-computing)

  (overview
    (manufacturer "Apple Computer")
    (launch-date "1984-01-24")
    (price "$2,495")
    (significance "First commercially successful GUI computer"))

  (hardware
    (processor "Motorola 68000" "8 MHz")
    (ram "128 KB")
    (rom "64 KB" "QuickDraw and Toolbox")
    (display "9-inch monochrome" "512x342 pixels")
    (storage "400 KB 3.5-inch floppy"))

  (key-team
    (burrell-smith
      (role "Hardware designer")
      (inspiration "Steve Wozniak's creative approach")
      (achievement "Integrated 68000 into Macintosh by December 1980")
      (design-philosophy "Crazy tricks all over the place")
      (efficiency "Less RAM than Lisa, more cost-efficient board"))

    (andy-hertzfeld
      (role "Technical lead, system software")
      (joined "Second programmer after Bud Tribble")
      (responsibilities
        "Overall system architecture"
        "Substantial portion of system code"
        "Integration lead for other programmers")
      (contributions
        "Much of the ROM code"
        "User Interface Toolbox"
        "Control Panel"
        "Scrapbook"
        "Device drivers and I/O system (1981)"
        "Windows, menus, buttons (1982)"
        "Ported Lisa code to Mac's smaller footprint"))

    (bill-atkinson
      (role "QuickDraw and MacPaint author")
      (contributions
        "QuickDraw graphics library"
        "MacPaint application"
        "LisaSketch predecessor")))

  (rom-philosophy
    (jobs-quote
      "We're a 192K-byte machine that deep-freezes 64K.")
    (hertzfeld-quote
      "If the programmers want to throw away 64K,
       then they're doing a dumb thing.")
    (contents
      "Complete QuickDraw picture language and interpreter"
      "Far more than typical 4-8 KB ROM of other computers"))

  (development-approach
    (language "Hand-coded 68000 assembly")
    (rationale "Three times more efficient than Pascal")
    (contrast "Lisa was mostly high-level Pascal"))

  (source-code
    (macpaint
      (author "Bill Atkinson")
      (started "Early 1983")
      (lines "5,822 lines Apple Pascal + 3,583 lines 68000 assembly")
      (predecessor "LisaSketch/SketchPad for Lisa"))

    (quickdraw
      (author "Bill Atkinson")
      (lines "17,101 lines in 36 files, all 68000 assembly")
      (significance "About one-third of original Mac OS")
      (description "Macintosh library for bit-mapped graphics"))

    (release
      (date "2010-07-20")
      (releaser "Computer History Museum")
      (catalyst "Andy Hertzfeld found code via former colleague, 2004")
      (source "Floppy disks built for Apple Lisa")
      (license "Non-commercial use, Apple Inc.")
      (download "https://computerhistory.org/blog/macpaint-and-quickdraw-source-code/")
      (github "https://github.com/computerhistory/Historical-Source-Code-MacPaint-Repository"
              "https://github.com/jrk/QuickDraw")))

  (resources
    (chm-macpaint "https://computerhistory.org/blog/macpaint-and-quickdraw-source-code/")
    (macpaint-github "https://github.com/computerhistory/Historical-Source-Code-MacPaint-Repository")
    (quickdraw-github "https://github.com/jrk/QuickDraw")
    (folklore "https://www.folklore.org/" "Andy Hertzfeld's Macintosh stories")))
