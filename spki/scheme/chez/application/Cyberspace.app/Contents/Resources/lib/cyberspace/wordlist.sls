;;; SPKI Scheme - Pronounceable Verification Codes
;;; Library of Cyberspace - Chez Port
;;;
;;; Provides human-readable fingerprints for public keys.
;;; Used during node enrollment (Memo-044) for verbal verification.
;;;
;;; Supports two modes:
;;;   FIPS-181: Automated Password Generator (federal compliance)
;;;   PGP:      Biometric word list (legacy/alternative)

(library (cyberspace wordlist)
  (export
    fips181-encode
    byte->syllable
    pubkey->syllables
    syllables->display
    byte->word
    pubkey->words
    words->display
    *verification-mode*
    even-words
    odd-words)

  (import (rnrs)
          (cyberspace crypto-ffi)
          (cyberspace chicken-compatibility blob)
          (cyberspace chicken-compatibility chicken))

  (define *verification-mode* 'fips-181)

  ;; Vowels and consonants for syllable construction
  (define vowels "aeiou")
  (define consonants "bcdfghjklmnpqrstvwxyz")

  (define (byte->syllable byte)
    "Convert a byte to a pronounceable syllable (FIPS-181 style)"
    (let* ((c1-idx (mod byte 21))
           (v-idx  (mod (div byte 21) 5))
           (c2-idx (mod (div byte 105) 21))
           (c1 (string-ref consonants c1-idx))
           (v  (string-ref vowels v-idx))
           (c2 (string-ref consonants (mod (+ c2-idx c1-idx) 21))))
      (string c1 v c2)))

  (define (bytes->fips181 bytes)
    (let loop ((i 0) (acc '()))
      (if (>= i (u8vector-length bytes))
          (apply string-append (reverse acc))
          (loop (+ i 1)
                (cons (byte->syllable (u8vector-ref bytes i)) acc)))))

  (define (fips181-encode data)
    "Encode arbitrary data as FIPS-181 pronounceable syllables"
    (let ((bytes (if (bytevector? data)
                     (blob->u8vector data)
                     data)))
      (bytes->fips181 bytes)))

  (define (pubkey->syllables pubkey)
    "Convert public key to FIPS-181 verification syllables."
    (let* ((hash (sha256-hash pubkey))
           (bytes (blob->u8vector hash)))
      (let loop ((i 0) (acc '()))
        (if (= i 4)
            (reverse acc)
            (loop (+ i 1)
                  (cons (byte->syllable (u8vector-ref bytes i)) acc))))))

  (define (syllables->display syllables)
    (string-join syllables "-"))

  ;; Even-position words (two syllables, 256 total)
  ;; Official PGP word list - Juola & Zimmermann 1995
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
    (vector-ref (if (even? position) even-words odd-words)
                (mod byte 256)))

  (define (pubkey->words pubkey)
    (let* ((hash (sha256-hash pubkey))
           (bytes (blob->u8vector hash)))
      (list (byte->word (u8vector-ref bytes 0) 0)
            (byte->word (u8vector-ref bytes 1) 1)
            (byte->word (u8vector-ref bytes 2) 2)
            (byte->word (u8vector-ref bytes 3) 3))))

  (define (words->display words)
    (string-join words "  "))

  (define (string-join strings sep)
    (if (null? strings) ""
        (let loop ((rest (cdr strings)) (acc (car strings)))
          (if (null? rest) acc
              (loop (cdr rest) (string-append acc sep (car rest)))))))

) ;; end library
