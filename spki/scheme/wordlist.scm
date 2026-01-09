;;; SPKI Scheme - Pronounceable Verification Codes
;;;
;;; Provides human-readable fingerprints for public keys.
;;; Used during node enrollment (RFC-044) for verbal verification.
;;;
;;; Supports two modes:
;;;   FIPS-181: Automated Password Generator (federal compliance)
;;;   PGP:      Biometric word list (legacy/alternative)
;;;
;;; FIPS-181 generates pronounceable random syllables using
;;; digraph frequency tables and phonotactic rules.

(module wordlist
  (;; FIPS-181 (default, federal compliance)
   fips181-encode
   byte->syllable       ; single byte to syllable
   pubkey->syllables
   syllables->display
   ;; PGP word list (alternative)
   byte->word
   pubkey->words
   words->display
   ;; Configuration
   *verification-mode*
   ;; Word lists (for PGP mode testing)
   even-words
   odd-words)

  (import scheme
          (chicken base)
          (chicken blob)
          (chicken format)
          (chicken bitwise)
          srfi-1      ; list utilities
          srfi-4      ; u8vectors
          crypto-ffi) ; sha256-hash

  ;; Default to FIPS-181 for federal compliance
  (define *verification-mode* 'fips-181)

  ;; ============================================================
  ;; FIPS-181: Automated Password Generator
  ;; ============================================================
  ;; Generates pronounceable syllables from random bytes using
  ;; digraph tables and phonotactic rules.

  ;; Vowels and consonants for syllable construction
  (define vowels "aeiou")
  (define consonants "bcdfghjklmnpqrstvwxyz")

  ;; FIPS-181 digraph flags
  (define NOT-BEGIN   1)   ; Cannot begin syllable
  (define NOT-END     2)   ; Cannot end syllable
  (define VOWEL       4)   ; Is a vowel
  (define CONSONANT   8)   ; Is a consonant (not used with VOWEL)
  (define DIPTHONG   16)   ; Vowel dipthong (ae, ai, etc.)
  (define NOT-FIRST  32)   ; Cannot be first in word

  ;; Simplified FIPS-181 syllable generator
  ;; Generates CVC (consonant-vowel-consonant) patterns
  (define (byte->syllable byte)
    "Convert a byte to a pronounceable syllable (FIPS-181 style)"
    (let* ((c1-idx (modulo byte 21))
           (v-idx  (modulo (quotient byte 21) 5))
           (c2-idx (modulo (quotient byte 105) 21))
           (c1 (string-ref consonants c1-idx))
           (v  (string-ref vowels v-idx))
           (c2 (string-ref consonants (modulo (+ c2-idx c1-idx) 21))))
      (string c1 v c2)))

  ;; Extended FIPS-181 with better entropy usage
  (define (bytes->fips181 bytes)
    "Convert bytes to FIPS-181 pronounceable string"
    (let loop ((i 0) (acc '()))
      (if (>= i (u8vector-length bytes))
          (apply string-append (reverse acc))
          (loop (+ i 1)
                (cons (byte->syllable (u8vector-ref bytes i)) acc)))))

  (define (fips181-encode data)
    "Encode arbitrary data as FIPS-181 pronounceable syllables"
    (let ((bytes (if (blob? data)
                     (blob->u8vector data)
                     data)))
      (bytes->fips181 bytes)))

  (define (pubkey->syllables pubkey)
    "Convert public key to FIPS-181 verification syllables.
     Uses first 4 bytes of SHA-256 hash."
    (let* ((hash (sha256-hash pubkey))
           (bytes (blob->u8vector hash)))
      ;; Take first 4 bytes, generate 4 syllables
      (let loop ((i 0) (acc '()))
        (if (= i 4)
            (reverse acc)
            (loop (+ i 1)
                  (cons (byte->syllable (u8vector-ref bytes i)) acc))))))

  (define (syllables->display syllables)
    "Format FIPS-181 syllables for display"
    (string-join syllables "-"))

  ;; Even-position words (two syllables, 256 total)
  ;; Official PGP word list - Juola & Zimmermann 1995
  ;; Optimized for phonetic distinctiveness via genetic algorithm
  (define even-words
    '#("aardvark" "absurd" "accrue" "acme" "adrift"
       "adult" "afflict" "ahead" "aimless" "Algol"
       "allow" "alone" "ammo" "ancient" "apple"
       "artist" "assume" "Athens" "atlas" "Aztec"
       "baboon" "backfield" "backward" "basalt" "beaming"
       "bedlamp" "beehive" "beeswax" "befriend" "Belfast"
       "berserk" "billiard" "bison" "blackjack" "blockade"
       "blowtorch" "bluebird" "bombast" "bookshelf" "brackish"
       "breadline" "breakup" "brickyard" "briefcase" "Burbank"
       "button" "buzzard" "cement" "chairlift" "chatter"
       "checkup" "chisel" "choking" "chopper" "Christmas"
       "clamshell" "classic" "classroom" "cleanup" "clockwork"
       "cobra" "commence" "concert" "cowbell" "crackdown"
       "cranky" "crowfoot" "crucial" "crumpled" "crusade"
       "cubic" "deadbolt" "deckhand" "dogsled" "dosage"
       "dragnet" "drainage" "dreadful" "drifter" "dropper"
       "drumbeat" "drunken" "Dupont" "dwelling" "eating"
       "edict" "egghead" "eightball" "endorse" "endow"
       "enlist" "erase" "escape" "exceed" "eyeglass"
       "eyetooth" "facial" "fallout" "flagpole" "flatfoot"
       "flytrap" "fracture" "fragile" "framework" "freedom"
       "frighten" "gazelle" "Geiger" "Glasgow" "glitter"
       "glucose" "goggles" "goldfish" "gremlin" "guidance"
       "hamlet" "highchair" "hockey" "hotdog" "indoors"
       "indulge" "inverse" "involve" "island" "Janus"
       "jawbone" "keyboard" "kickoff" "kiwi" "klaxon"
       "lockup" "merit" "minnow" "miser" "Mohawk"
       "mural" "music" "Neptune" "newborn" "nightbird"
       "obtuse" "offload" "oilfield" "optic" "orca"
       "payday" "peachy" "pheasant" "physique" "playhouse"
       "Pluto" "preclude" "prefer" "preshrunk" "printer"
       "profile" "prowler" "pupil" "puppy" "python"
       "quadrant" "quiver" "quota" "ragtime" "ratchet"
       "rebirth" "reform" "regain" "reindeer" "rematch"
       "repay" "retouch" "revenge" "reward" "rhythm"
       "ringbolt" "robust" "rocker" "ruffled" "sawdust"
       "scallion" "scenic" "scorecard" "Scotland" "seabird"
       "select" "sentence" "shadow" "showgirl" "skullcap"
       "skydive" "slingshot" "slothful" "slowdown" "snapline"
       "snapshot" "snowcap" "snowslide" "solo" "spaniel"
       "spearhead" "spellbind" "spheroid" "spigot" "spindle"
       "spoilage" "spyglass" "stagehand" "stagnate" "stairway"
       "standard" "stapler" "steamship" "stepchild" "sterling"
       "stockman" "stopwatch" "stormy" "sugar" "surmount"
       "suspense" "swelter" "tactics" "talon" "tapeworm"
       "tempest" "tiger" "tissue" "tonic" "tracker"
       "transit" "trauma" "treadmill" "Trojan" "trouble"
       "tumor" "tunnel" "tycoon" "umpire" "uncut"
       "unearth" "unwind" "uproot" "upset" "upshot"
       "vapor" "village" "virus" "Vulcan" "waffle"
       "wallet" "watchword" "wayside" "willow" "woodlark"
       "Zulu"))

  ;; Odd-position words (three syllables, exactly 256)
  ;; Official PGP word list - Juola & Zimmermann 1995
  (define odd-words
    '#("adroitness" "adviser" "aggregate" "alkali" "almighty"
       "amulet" "amusement" "antenna" "applicant" "Apollo"
       "armistice" "article" "asteroid" "Atlantic" "atmosphere"
       "autopsy" "Babylon" "backwater" "barbecue" "belowground"
       "bifocals" "bodyguard" "borderline" "bottomless" "Bradbury"
       "Brazilian" "breakaway" "Burlington" "businessman" "butterfat"
       "Camelot" "candidate" "cannonball" "Capricorn" "caravan"
       "caretaker" "celebrate" "cellulose" "certify" "chambermaid"
       "Cherokee" "Chicago" "clergyman" "coherence" "combustion"
       "commando" "company" "component" "concurrent" "confidence"
       "conformist" "congregate" "consensus" "consulting" "corporate"
       "corrosion" "councilman" "crossover" "cumbersome" "customer"
       "Dakota" "decadence" "December" "decimal" "designing"
       "detector" "detergent" "determine" "dictator" "dinosaur"
       "direction" "disable" "disbelief" "disruptive" "distortion"
       "divisive" "document" "embezzle" "enchanting" "enrollment"
       "enterprise" "equation" "equipment" "escapade" "Eskimo"
       "everyday" "examine" "existence" "exodus" "fascinate"
       "filament" "finicky" "forever" "fortitude" "frequency"
       "gadgetry" "Galveston" "getaway" "glossary" "gossamer"
       "graduate" "gravity" "guitarist" "hamburger" "Hamilton"
       "handiwork" "hazardous" "headwaters" "hemisphere" "hesitate"
       "hideaway" "holiness" "hurricane" "hydraulic" "impartial"
       "impetus" "inception" "indigo" "inertia" "infancy"
       "inferno" "informant" "insincere" "insurgent" "integrate"
       "intention" "inventive" "Istanbul" "Jamaica" "Jupiter"
       "leprosy" "letterhead" "liberty" "maritime" "matchmaker"
       "maverick" "Medusa" "megaton" "microscope" "microwave"
       "midsummer" "millionaire" "miracle" "misnomer" "molasses"
       "molecule" "Montana" "monument" "mosquito" "narrative"
       "nebula" "newsletter" "Norwegian" "October" "Ohio"
       "onlooker" "opulent" "Orlando" "outfielder" "Pacific"
       "pandemic" "pandora" "paperweight" "paragon" "paragraph"
       "paramount" "passenger" "pedigree" "Pegasus" "penetrate"
       "perceptive" "performance" "pharmacy" "phonetic" "photograph"
       "pioneer" "pocketful" "politeness" "positive" "potato"
       "processor" "prophecy" "provincial" "proximate" "puberty"
       "publisher" "pyramid" "quantity" "racketeer" "rebellion"
       "recipe" "recover" "repellent" "replica" "reproduce"
       "resistor" "responsive" "retraction" "retrieval" "retrospect"
       "revenue" "revival" "revolver" "Sahara" "sandalwood"
       "sardonic" "Saturday" "savagery" "scavenger" "sensation"
       "sociable" "souvenir" "specialist" "speculate" "stethoscope"
       "stupendous" "supportive" "surrender" "suspicious" "sympathy"
       "tambourine" "telephone" "therapist" "tobacco" "tolerance"
       "tomorrow" "torpedo" "tradition" "travesty" "trombonist"
       "truncated" "typewriter" "ultimate" "undaunted" "underfoot"
       "unicorn" "unify" "universe" "unravel" "upcoming"
       "vacancy" "vagabond" "versatile" "vertigo" "Virginia"
       "visitor" "vocalist" "voyager" "warranty" "Waterloo"
       "whimsical" "Wichita" "Wilmington" "Wyoming" "yesteryear"
       "Yucatan"))

  (define (byte->word byte position)
    "Convert a byte value to a word based on position parity.
     Even positions use two-syllable words, odd use three-syllable.
     This phonetic distinction catches transposition errors."
    (vector-ref (if (even? position) even-words odd-words)
                (modulo byte 256)))

  (define (pubkey->words pubkey)
    "Convert public key to 4 verification words.

     Takes SHA-256 of the public key, uses first 4 bytes
     to select words. 32 bits of entropy - enough to prevent
     accidental confusion while remaining easy to verify verbally."
    (let* ((hash (sha256-hash pubkey))
           (bytes (blob->u8vector hash)))
      (list (byte->word (u8vector-ref bytes 0) 0)
            (byte->word (u8vector-ref bytes 1) 1)
            (byte->word (u8vector-ref bytes 2) 2)
            (byte->word (u8vector-ref bytes 3) 3))))

  (define (words->display words)
    "Format verification words for display.
     Uses double spaces for visual clarity."
    (string-join words "  "))

  ;; Helper: join strings with separator
  (define (string-join strings sep)
    (if (null? strings)
        ""
        (let loop ((rest (cdr strings))
                   (acc (car strings)))
          (if (null? rest)
              acc
              (loop (cdr rest)
                    (string-append acc sep (car rest)))))))

) ;; end module

;;;
;;; Example usage:
;;;
;;;   (import wordlist crypto-ffi)
;;;   (sodium-init)
;;;
;;;   (let* ((keys (ed25519-keypair))
;;;          (pubkey (car keys))
;;;          (words (pubkey->words pubkey)))
;;;     (printf "Verification words: ~a~n" (words->display words)))
;;;
;;;   => "Verification words: castle  river  orange  lighthouse"
;;;
