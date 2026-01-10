;; Apple Lisa Research
;; Compiled 2026-01-09

(research
  (title "Apple Lisa")
  (date "2026-01-09")
  (category classic-computing)

  (overview
    (manufacturer "Apple Computer")
    (launch-date "1983-01-19")
    (price "$9,995")
    (development-time "5 years")
    (significance "First Apple hardware with graphical user interface"))

  (hardware
    (processor "Motorola 68000" "5 MHz")
    (ram "1 MB" "expandable to 2 MB")
    (display "12-inch monochrome" "720x364 pixels")
    (storage "5.25-inch Twiggy floppy drives" "ProFile hard drive")
    (weight "48 lbs")
    (expansion-slots "3"))

  (architecture-notes
    (rom-usage
      "Unlike Mac, Lisa ROM is minimal"
      "Used mainly for POST and booting"
      "Limited to reading blocks from floppy or Profile")
    (memory-map
      (system-rom "C000-C7FF")))

  (operating-systems
    (lisa-os "Lisa 7/7" "Native GUI OS")
    (macworks "Can run up to System 7.5 with hardware/RAM modifications")
    (xenix "Microsoft Xenix Unix"))

  (source-code-release
    (date "2023-01-19" "40th anniversary")
    (releaser "Computer History Museum")
    (contents "Operating system and applications software")
    (license "Non-commercial use, Apple Inc.")
    (download "https://info.computerhistory.org/apple-lisa-code")
    (notes
      "American Heritage Dictionary for spell checker not included"
      "Part of CHM Art of Code series"))

  (macintosh-relationship
    (quote-hertzfeld
      "The Lisa used more or less industry-standard techniques,
       whereas Burrell Smith was inspired by Woz and used crazy
       tricks all over the place.")
    (lisa-advantages
      "Hard disk support"
      "Up to 2 MB RAM"
      "Expansion slots"
      "Larger, higher resolution display")
    (lisa-software "Mostly written in Pascal")
    (mac-approach "Hand-coded 68000 assembly for efficiency"))

  (emulation
    (lisaem
      (description "First fully functional Lisa Emulator")
      (author "Ray Arachelian")
      (github "https://github.com/rayarachelian/lisaem")
      (website "https://lisa.sunder.net/"))
    (mame "Also supports Lisa emulation"))

  (rom-images
    (source "https://archive.org/details/apple-lisa-h-1983")
    (description "Rev. H ROMs"))

  (documentation
    (david-craig "Extensive Lisa documentation, invaluable for emulation")
    (chm-article "Museum released detailed significance document with code"))

  (resources
    (chm-download "https://info.computerhistory.org/apple-lisa-code")
    (lisa-emulator "https://lisa.sunder.net/")
    (archive-roms "https://archive.org/details/apple-lisa-h-1983")))
