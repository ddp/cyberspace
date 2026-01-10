;; Sol-20 and Electric Pencil Research
;; Compiled 2026-01-09

(research
  (title "Processor Technology Sol-20 and Electric Pencil")
  (date "2026-01-09")
  (category classic-computing)

  (sol-20
    (manufacturer "Processor Technology Corporation")
    (designer "Lee Felsenstein")
    (year 1976)
    (processor "Intel 8080" "8 MHz")
    (pronunciation "Saul" "per Lee Felsenstein")

    (display
      (module "VDM-1")
      (description "First graphics card for S-100 bus")
      (resolution "64 characters x 16 lines" "expandable to 80 columns")
      (character-set "Full ASCII upper/lower case, graphics characters")
      (video-ram "CC00-CFFF" "1K shared memory")
      (notes "Clean video timing, quality character generator ROM"))

    (character-generator
      (rom-file "6575.bin")
      (size "0x0800" "2KB")
      (load-address "0x0800")
      (crc "cfdb76c2")
      (sha1 "ab00798161d13f07bee3cf0e0070a2f0a805591f")
      (status "BAD_DUMP - needs verification")
      (contributors "Phil Lord created binary ROM images for both versions")
      (notes "Characters moved back to original 7x9 matrix positions"))

    (personality-modules
      (description "Removable ROM cards, up to 2KB EPROM")
      (origin "Named by Don Lancaster")
      (inventor "Lee Felsenstein")
      (types
        (solos "Standard - cassette names, TSAVE, TCAT, TXEC")
        (consol "Stripped down 1KB version")
        (cuter "For other 8080 machines with PT peripherals")
        (bootload "For Helios II disk bootstrap")
        (soled "Smart terminal with offline editing")
        (dpmon "Third-party enhanced memory commands")))

    (memory-map
      (system-rom "C000-C7FF" "Personality modules mapped here")
      (system-ram "C800-CBFF")
      (display-ram "CC00-CFFF" "Shared with VDM-1"))

    (notable-software
      (target "Steve Dompier, 1977" "ASCII graphics game, VDM-1 showcase")
      (trek-80 "Steve Dompier, 1977" "Real-time Star Trek game")
      (chess "Processor Technology" "Middle-of-road chess program")
      (electric-pencil "Michael Shrayer, 1976" "First microcomputer word processor"))

    (radio-sound
      (description "AM radio tuned to CPU RF interference")
      (demonstrator "Steve Dompier at Homebrew Computer Club")
      (games-with-sound target trek-80)))

  (electric-pencil
    (author "Michael Shrayer")
    (year 1976)
    (description "First word processor for microcomputers")
    (innovation "First to implement word wrap")
    (requirements "8K RAM" "Intel 8080 or Zilog Z80")
    (platforms "Altair 8800" "Sol-20" "NorthStar Horizon" "TRS-80" "IBM PC")
    (versions 78)

    (loading-commands
      (auto-start "XE PENCL")
      (manual "GE PENCL" "then EX 0"))

    (historical-note
      "Jerry Pournelle was the first author to publish
       a portion of a book written with a word processor
       on a personal computer, using Electric Pencil"))

  (helios-ii
    (manufacturer "Processor Technology")
    (designer "Lee Felsenstein")
    (year "circa 1976")
    (type "Dual 8-inch floppy disk system")
    (mechanism "Persci 270")
    (features
      (single-motor "Spins both disks simultaneously")
      (shared-positioner "Single voice coil moves both heads")
      (disk-to-disk "Copy without CPU intervention")
      (fast-seek "Voice coil head positioning"))
    (capacity "384,000 bytes per diskette" "~750KB total")
    (price "$1,895 kit" "$2,295 assembled")
    (operating-system "PTDOS")
    (challenges
      "Unreliable, required periodic recalibration"
      "Xerox canceled Diablo floppy development"
      "Undercut by North Star 5.25-inch drives"))

  (emulation
    (solace
      (description "Sol Anachronistic Computer Emulation")
      (author "Jim Battle")
      (platform "Windows")
      (includes "SOLOS ROM, sample programs"))
    (mame
      (driver "ptcsol.cpp")
      (rom-file "sol20.zip" "~11KB")
      (cassette-software "sol20_cass.zip" "~26.5MB")))

  (resources
    (sol20-org "http://www.sol20.org/" "Main archive site")
    (manual-pdf "https://sol20.org/manuals/pencil.pdf")
    (personality-modules "https://sol20.org/personality.html")
    (programs "http://www.sol20.org/programs.html")
    (tosec-archive "https://archive.org/details/PTC_Sol_Terminal_Computer_SOL-20_TOSEC_2012_04_23")
    (digibarn-manual "https://www.digibarn.com/collections/manuals/electric-pencil/index.html")
    (lee-felsenstein-article "https://deramp.com/sol20.org/articles/ROM_7_1977.pdf")))
