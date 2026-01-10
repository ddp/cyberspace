;; DEC PRISM and MICA Deep Dive
;; Compiled 2026-01-09

(research
  (title "DEC PRISM Architecture and MICA Operating System")
  (date "2026-01-09")
  (category classic-computing)

  (overview
    (prism "Parallel Reduced Instruction Set Machine")
    (type "32-bit RISC architecture")
    (company "Digital Equipment Corporation")
    (development "1982-1988")
    (status "Canceled July 1988")
    (legacy "Evolved into DEC Alpha" "Inspired Windows NT"))

  (precursor-projects
    (description "Four separate RISC projects consolidated into PRISM")

    (titan
      (location "Western Research Laboratory, Palo Alto")
      (start "1982")
      (supervisor "Forest Baskett")
      (type "High-speed ECL design"))

    (safe
      (name "Streamlined Architecture for Fast Execution")
      (start "1983")
      (leaders "Alan Kotok" "David Orbits")
      (type "64-bit design")
      (target "VMS"))

    (hr-32
      (name "Hudson RISC 32-bit")
      (start "1984")
      (location "Hudson, MA semiconductor fab")
      (leaders "Rich Witek" "Dan Dobberpuhl")
      (purpose "VAX co-processor"))

    (cascade
      (start "1984")
      (location "DECwest, Bellevue, Washington")
      (leader "Dave Cutler"))

    (consolidation
      (date "May 1985")
      (chief-architect "Rich Witek")
      (first-draft "August 1985")))

  (specification-team
    (members
      "Dave Cutler"
      "Dave Orbits"
      "Rich Witek"
      "Dileep Bhandarkar"
      "Wayne Cardoza")
    (completion "98% done 1985-86")
    (validation "Pete Benoit simulations on large VAXcluster"))

  (architecture
    (word-size "32-bit" "initially 64-bit, later downsized")
    (instruction-format "Fixed 32-bit")
    (instruction-encoding
      "6 highest bits + 5 lowest bits = opcode"
      "21 bits for constant or register locations")

    (registers
      (general-purpose 64 "32-bit" "vs 32 in MIPS")
      (vector 16 "64-bit" "for vector processing")
      (epicode 22 "32-bit" "dedicated to Epicode"))

    (address-space "45-bit")

    (floating-point
      (status "No integrated FPU")
      (design "FPU design incomplete at cancellation"))

    (implementations
      (crystal
        (developer "DECwest")
        (type "High-end ECL"))
      (microprism
        (developer "Semiconductor Advanced Development")
        (type "CMOS")
        (performance "50-80 MHz observed in samples")
        (comparison "vs R2000's 16-20 MHz"))))

  (epicode
    (name "Extended Processor Instruction Code")
    (description "Software-defined microcode instructions")
    (purpose
      "Stable ABI across implementations"
      "VAX instruction emulation"
      "OS-specific privileged operations")
    (registers 22 "32-bit dedicated")
    (evolution "Became Alpha PALcode"))

  (microprism-chip
    (lead-architect "Rich Witek")
    (paper "A 50 MIPS (Peak) 32/64b Microprocessor"
           "Robert Conrad et al."
           "ISSCC Digest of Technical Papers"
           "February 1989, pp. 76-77")
    (alu-completion "April 1988")
    (status-at-cancel
      "ALU samples fabricated and mostly working"
      "FPU and MMU designs incomplete"))

  (mica
    (name "MICA" "codename, no official expansion")
    (type "Multipersonality operating system")
    (leader "Dave Cutler")

    (design-goals
      "Migration path for VAX/VMS customers"
      "Run VMS and ULTRIX on same kernel"
      "Full access to both APIs from any application")

    (architecture
      (kernel "Common kernel for all personalities")
      (subsystems "VMS and ULTRIX as user-mode servers")
      (note "Not full microkernel like Mach"))

    (outcome
      "Impossible to provide full compatibility to both simultaneously"
      "Plan scrapped for standalone PRISM ULTRIX"))

  (emerald
    (description "First MICA implementation to port VMS onto PRISM")
    (variants
      (mips-port "VMS to MIPS-based systems")
      (ia32-port "VMS to Intel 386/486/Pentium"
                 "Per Charlie Matco via Terry Shannon"))
    (canceled "March 1988"))

  (cancellation
    (date "July 1988")
    (meeting "Executive Committee review, described as acrimonious")
    (decision
      "Cancel PRISM"
      "Continue with MIPS workstations (became DECstation 3100)"
      "Continue high-end VAX (Aquarius/VAX 9000)")

    (rationale
      "MIPS R3000 faster to market (90 days to prototype)"
      "DEC financial situation")

    (irony
      "microPRISM samples showed 50-80 MHz capability"
      "Significant performance advantage over competition"
      "Silicon was mostly working"))

  (dave-cutler
    (born "1942-03-13" "Lansing/DeWitt, Michigan")
    (education "Olivet College, 1965")

    (career
      (dupont "1965-1971"
              "Technical writer, then GPSS development"
              "Fixed EXEC-II bugs on Univac 1108"
              "First exposure to operating systems")

      (dec-maynard "1971-1981"
                   "RSX-11M for PDP-11 (preemptive multitasking, modular design)"
                   "VAX/VMS technical lead with Hustvedt and Lipman (1975)"
                   "Blue Ribbon Committee for VAX architecture"
                   "PL/1 and C compilers")

      (dec-seattle "1981-1988"
                   "Founded DECwest engineering lab"
                   "Embedded real-time OS for chip-based VAX"
                   "MicroVAX I development"
                   "CASCADE project (1984)"
                   "PRISM chief architect (1985)"
                   "MICA and Emerald leader")

      (departure
        (date "October 1988")
        (intermediary "Nathan Myhrvold introduced to Bill Gates")
        (recruited-by "Steve Ballmer")))

    (microsoft
      (project "Windows NT")
      (mica-influence
        "Multiple OS APIs on common kernel (Win32, OS/2, POSIX)"
        "Kernel/Executive separation"
        "Object Manager abstraction"
        "Multithreading and SMP support"))

    (recognition
      "National Academy of Engineering member"
      "National Medal of Technology and Innovation (2007)"))

  (alpha-evolution
    (start "1989" "mid-year, after PRISM cancellation")
    (origin "Ken Olsen started new project at same meeting that canceled PRISM")
    (architects "Rich Witek" "Richard Sites")

    (relationship-to-prism
      "Used most basic PRISM concepts"
      "Re-tuned for VMS compatibility without conversion"
      "Upgraded to full 64-bit (from PRISM's 32-bit)"
      "Epicode became PALcode")

    (first-chip "DECchip 21064" "1992")
    (industry-joke "AXP = Almost eXactly PRISM"))

  (palcode
    (name "Privileged Architecture Library code")
    (origin "Evolved from PRISM Epicode")
    (description "Alpha machine code in special privileged mode")
    (features
      "Access to implementation-specific internal registers"
      "Cache management"
      "TLB miss handling"
      "Interrupt and exception handling")
    (os-specific "Different PALcode for OpenVMS, Tru64 UNIX, Windows NT")
    (role "Between microcode and hardware emulator"))

  (legal-aftermath
    (dec-microsoft
      "DEC alleged Windows NT incorporated MICA technology"
      "Settlement reached"
      "Microsoft licensed Alpha architecture"))

  (resources
    (wikipedia-prism "https://en.wikipedia.org/wiki/DEC_PRISM")
    (wikipedia-mica "https://en.wikipedia.org/wiki/DEC_MICA")
    (neil-rieck "https://neilrieck.net/docs/dave_cutler-prism-mica-emerald-etc.html")
    (mark-smotherman "https://people.computing.clemson.edu/~mark/prism.html")
    (cutler-oral-history "https://www.computerhistory.org/collections/catalog/102717163")
    (dobberpuhl-interview "https://queue.acm.org/detail.cfm?id=957732")))
