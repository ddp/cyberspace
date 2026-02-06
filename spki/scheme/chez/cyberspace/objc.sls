;;; Objective-C Runtime Bridge for Chez Scheme
;;; Library of Cyberspace - Chez Port
;;;
;;; Replaces Chicken's compile-to-C Objective-C interop with an
;;; explicit bridge through the ObjC runtime's C API.
;;;
;;; Architecture:
;;;   Chez Scheme -> foreign-procedure -> libobjc-bridge.dylib -> objc_msgSend -> Cocoa
;;;
;;; The bridge provides:
;;;   - Class/selector lookup
;;;   - Typed message send (ptr, int, double, bool, void returns)
;;;   - NSString/NSNumber/NSArray/NSDictionary creation
;;;   - Runtime class creation (for delegates and callbacks)
;;;   - NSApplication bootstrap
;;;   - Autorelease pool management
;;;
;;; Usage:
;;;   (import (cyberspace objc))
;;;   (objc-init!)
;;;   (with-autorelease-pool
;;;     (let* ((s (nsstring "Hello from Chez!"))
;;;            (len (msg/int s "length")))
;;;       (printf "length: ~d~n" len)))
;;;
;;; Heritage: This is the piece Chicken gives you for free because csc
;;; compiles Scheme to C.  For Chez, we build it ourselves.

(library (cyberspace objc)
  (export
    ;; Initialization
    objc-init!

    ;; Class & selector
    objc-class objc-sel

    ;; Alloc & init
    objc-alloc objc-init-obj

    ;; Message send by return type
    msg       msg/1     msg/2     msg/3       ; -> pointer (id)
    msg/int   msg/int1  msg/int-long          ; -> integer
    msg/double                                ; -> double
    msg/bool  msg/bool1                       ; -> boolean
    msg/void  msg/void1 msg/void2             ; -> void
    msg/void-int msg/void-double msg/void-bool
    msg/rect-bool msg/void-rect-bool          ; -> rect args

    ;; NSString
    nsstring nsstring->string

    ;; NSNumber
    nsnumber/int nsnumber/double

    ;; NSArray
    nsarray nsarray-count nsarray-ref

    ;; NSDictionary
    nsdict

    ;; Autorelease pool
    with-autorelease-pool pool-push pool-pop

    ;; Memory management
    objc-retain objc-release

    ;; Runtime class creation
    objc-create-class objc-add-method! objc-add-ivar!
    objc-register-class!

    ;; Ivar access
    objc-set-ivar! objc-get-ivar

    ;; Introspection
    objc-class-name objc-responds-to? objc-is-kind-of?
    objc-description

    ;; NSApplication
    nsapp nsapp-set-policy! nsapp-activate! nsapp-run! nsapp-terminate!

    ;; Null
    objc-null objc-null?)

  (import (rnrs)
          (only (chezscheme)
                load-shared-object foreign-procedure
                lock-object foreign-callable
                make-parameter parameterize
                printf format void
                include guard with-exception-handler))

  ;; ============================================================
  ;; Library Loading
  ;; ============================================================

  ;; Path to the bridge dylib -- set before calling objc-init!
  ;; or let it search relative to the library.
  (define *bridge-loaded* #f)

  (define (objc-init!)
    "Load the Objective-C bridge shared library.
     Must be called before any other objc- functions.
     Safe to call multiple times (idempotent)."
    (unless *bridge-loaded*
      ;; Try several locations
      (let loop ((paths '("./libobjc-bridge.dylib"
                          "../libobjc-bridge.dylib"
                          "libobjc-bridge.dylib")))
        (if (null? paths)
            (error 'objc-init!
                   "Cannot find libobjc-bridge.dylib -- run build-objc-bridge.sh")
            (guard (exn [#t (loop (cdr paths))])
              (load-shared-object (car paths))
              (set! *bridge-loaded* #t))))))

  ;; ============================================================
  ;; Null Pointer
  ;; ============================================================

  (define objc-null 0)

  (define (objc-null? obj)
    "Check if an Objective-C object pointer is nil."
    (or (eqv? obj 0) (not obj)))

  ;; ============================================================
  ;; Foreign Procedure Declarations
  ;; ============================================================

  ;; Class & Selector
  (define %class       (foreign-procedure "bridge_class" (string) void*))
  (define %sel         (foreign-procedure "bridge_sel"   (string) void*))

  ;; Alloc & Init
  (define %alloc       (foreign-procedure "bridge_alloc" (void*) void*))
  (define %init        (foreign-procedure "bridge_init"  (void*) void*))

  ;; Message Send - Pointer Return
  (define %send        (foreign-procedure "bridge_send"     (void* void*) void*))
  (define %send-1      (foreign-procedure "bridge_send_1"   (void* void* void*) void*))
  (define %send-2      (foreign-procedure "bridge_send_2"   (void* void* void* void*) void*))
  (define %send-3      (foreign-procedure "bridge_send_3"   (void* void* void* void* void*) void*))

  ;; Message Send - Integer Return
  (define %send-int    (foreign-procedure "bridge_send_int"      (void* void*) integer-64))
  (define %send-int-1  (foreign-procedure "bridge_send_int_1"    (void* void* void*) integer-64))
  (define %send-int-l  (foreign-procedure "bridge_send_int_long" (void* void* integer-64) integer-64))

  ;; Message Send - Double Return
  (define %send-dbl    (foreign-procedure "bridge_send_double" (void* void*) double))

  ;; Message Send - Boolean Return
  (define %send-bool   (foreign-procedure "bridge_send_bool"   (void* void*) int))
  (define %send-bool-1 (foreign-procedure "bridge_send_bool_1" (void* void* void*) int))

  ;; Message Send - Void Return
  (define %send-void   (foreign-procedure "bridge_send_void"        (void* void*) void))
  (define %send-void-1 (foreign-procedure "bridge_send_void_1"      (void* void* void*) void))
  (define %send-void-2 (foreign-procedure "bridge_send_void_2"      (void* void* void* void*) void))
  (define %send-void-i (foreign-procedure "bridge_send_void_int"    (void* void* integer-64) void))
  (define %send-void-d (foreign-procedure "bridge_send_void_double" (void* void* double) void))
  (define %send-void-b (foreign-procedure "bridge_send_void_bool"   (void* void* int) void))

  ;; Message Send - Rect args
  (define %send-rect-b
    (foreign-procedure "bridge_send_rect_bool"
                       (void* void* double double double double int) void*))
  (define %send-void-rect-b
    (foreign-procedure "bridge_send_void_rect_bool"
                       (void* void* double double double double int) void))

  ;; NSString
  (define %nsstring     (foreign-procedure "bridge_nsstring"      (string) void*))
  (define %nsstring-utf8 (foreign-procedure "bridge_nsstring_utf8" (void*) string))

  ;; NSNumber
  (define %nsnumber-int (foreign-procedure "bridge_nsnumber_int"    (integer-64) void*))
  (define %nsnumber-dbl (foreign-procedure "bridge_nsnumber_double" (double) void*))

  ;; NSArray
  (define %array-count  (foreign-procedure "bridge_array_count" (void*) integer-64))
  (define %array-at     (foreign-procedure "bridge_array_at"    (void* integer-64) void*))

  ;; Autorelease Pool
  (define %pool-push    (foreign-procedure "bridge_pool_push" () void*))
  (define %pool-pop     (foreign-procedure "bridge_pool_pop"  (void*) void))

  ;; Memory Management
  (define %retain       (foreign-procedure "bridge_retain"  (void*) void*))
  (define %release      (foreign-procedure "bridge_release" (void*) void))

  ;; Runtime Class Creation
  (define %create-class (foreign-procedure "bridge_create_class"    (string string) void*))
  (define %add-method   (foreign-procedure "bridge_add_method"      (void* void* void* string) int))
  (define %add-ivar     (foreign-procedure "bridge_add_ivar"        (void* string integer-64 unsigned-8 string) int))
  (define %register     (foreign-procedure "bridge_register_class"  (void*) void))

  ;; Ivar Access
  (define %set-ivar     (foreign-procedure "bridge_set_ivar_ptr" (void* string void*) void))
  (define %get-ivar     (foreign-procedure "bridge_get_ivar_ptr" (void* string) void*))

  ;; Introspection
  (define %class-name   (foreign-procedure "bridge_class_name"   (void*) string))
  (define %responds-to  (foreign-procedure "bridge_responds_to"  (void* void*) int))
  (define %is-kind-of   (foreign-procedure "bridge_is_kind_of"   (void* void*) int))
  (define %description  (foreign-procedure "bridge_description"  (void*) string))

  ;; NSApplication
  (define %nsapp        (foreign-procedure "bridge_nsapp"            () void*))
  (define %nsapp-policy (foreign-procedure "bridge_nsapp_set_policy" (int) void))
  (define %nsapp-activate (foreign-procedure "bridge_nsapp_activate" () void))
  (define %nsapp-run    (foreign-procedure "bridge_nsapp_run"        () void))
  (define %nsapp-term   (foreign-procedure "bridge_nsapp_terminate"  () void))

  ;; ============================================================
  ;; Public API - Class & Selector
  ;; ============================================================

  (define (objc-class name)
    "Look up an Objective-C class by name.
     (objc-class \"NSString\") -> class pointer"
    (let ((cls (%class name)))
      (when (objc-null? cls)
        (error 'objc-class "Class not found" name))
      cls))

  (define (objc-sel name)
    "Register/look up a selector by name.
     (objc-sel \"initWithFrame:display:\") -> selector"
    (%sel name))

  ;; ============================================================
  ;; Public API - Alloc & Init
  ;; ============================================================

  (define (objc-alloc cls)
    "Allocate an uninitialized instance of a class.
     (objc-alloc (objc-class \"NSMutableArray\")) -> raw instance"
    (%alloc cls))

  (define (objc-init-obj obj)
    "Send -init to an allocated object.
     Always use the return value -- class clusters may substitute.
     (objc-init-obj (objc-alloc cls)) -> initialized instance"
    (%init obj))

  ;; ============================================================
  ;; Public API - Message Send
  ;;
  ;; Named by return type:
  ;;   msg       -> id (pointer)   msg/int   -> integer
  ;;   msg/double -> double         msg/bool  -> boolean (#t/#f)
  ;;   msg/void  -> void
  ;;
  ;; Suffix indicates arg count/types:
  ;;   msg/1  = 1 pointer arg    msg/int-long = 1 integer arg
  ;;   msg/void-double = void return, 1 double arg
  ;; ============================================================

  ;; Pointer return
  (define (msg obj sel)       (%send obj sel))
  (define (msg/1 obj sel a)   (%send-1 obj sel a))
  (define (msg/2 obj sel a b) (%send-2 obj sel a b))
  (define (msg/3 obj sel a b c) (%send-3 obj sel a b c))

  ;; Integer return
  (define (msg/int obj sel)     (%send-int obj sel))
  (define (msg/int1 obj sel a)  (%send-int-1 obj sel a))
  (define (msg/int-long obj sel a) (%send-int-l obj sel a))

  ;; Double return
  (define (msg/double obj sel) (%send-dbl obj sel))

  ;; Boolean return (convert C int to Scheme boolean)
  (define (msg/bool obj sel)
    (not (zero? (%send-bool obj sel))))
  (define (msg/bool1 obj sel a)
    (not (zero? (%send-bool-1 obj sel a))))

  ;; Void return
  (define (msg/void obj sel)       (%send-void obj sel))
  (define (msg/void1 obj sel a)    (%send-void-1 obj sel a))
  (define (msg/void2 obj sel a b)  (%send-void-2 obj sel a b))
  (define (msg/void-int obj sel n) (%send-void-i obj sel n))
  (define (msg/void-double obj sel d) (%send-void-d obj sel d))
  (define (msg/void-bool obj sel b) (%send-void-b obj sel (if b 1 0)))

  ;; Rect args
  (define (msg/rect-bool obj sel x y w h flag)
    (%send-rect-b obj sel x y w h (if flag 1 0)))
  (define (msg/void-rect-bool obj sel x y w h flag)
    (%send-void-rect-b obj sel x y w h (if flag 1 0)))

  ;; ============================================================
  ;; Public API - NSString
  ;; ============================================================

  (define (nsstring str)
    "Create an NSString from a Scheme string.
     (nsstring \"hello\") -> NSString*"
    (%nsstring str))

  (define (nsstring->string nsstr)
    "Extract a Scheme string from an NSString.
     (nsstring->string ns) -> \"hello\""
    (%nsstring-utf8 nsstr))

  ;; ============================================================
  ;; Public API - NSNumber
  ;; ============================================================

  (define (nsnumber/int n)
    "Create an NSNumber from an integer."
    (%nsnumber-int n))

  (define (nsnumber/double d)
    "Create an NSNumber from a double."
    (%nsnumber-dbl d))

  ;; ============================================================
  ;; Public API - NSArray
  ;; ============================================================

  (define (nsarray-count arr)
    "Get the count of an NSArray."
    (%array-count arr))

  (define (nsarray-ref arr idx)
    "Get element at index from NSArray."
    (%array-at arr idx))

  (define (nsarray . items)
    "Create an NSArray from Scheme arguments.
     Items must already be Objective-C objects (id pointers).
     (nsarray (nsstring \"a\") (nsstring \"b\")) -> NSArray*"
    (let* ((arr (objc-init-obj (objc-alloc (objc-class "NSMutableArray"))))
           (add-sel (objc-sel "addObject:")))
      (for-each (lambda (item)
                  (msg/void1 arr add-sel item))
                items)
      arr))

  ;; ============================================================
  ;; Public API - NSDictionary
  ;; ============================================================

  (define (nsdict . pairs)
    "Create an NSDictionary from key-value pairs.
     Keys and values must be Objective-C objects.
     (nsdict (nsstring \"key\") (nsstring \"val\")) -> NSDictionary*"
    (let* ((dict (objc-init-obj (objc-alloc (objc-class "NSMutableDictionary"))))
           (set-sel (objc-sel "setObject:forKey:")))
      (let loop ((rest pairs))
        (unless (null? rest)
          (when (null? (cdr rest))
            (error 'nsdict "Odd number of arguments -- need key-value pairs"))
          (msg/void2 dict set-sel (cadr rest) (car rest))
          (loop (cddr rest))))
      dict))

  ;; ============================================================
  ;; Public API - Autorelease Pool
  ;; ============================================================

  (define (pool-push) (%pool-push))
  (define (pool-pop pool) (%pool-pop pool))

  (define-syntax with-autorelease-pool
    (syntax-rules ()
      [(_ body ...)
       (let ((pool (pool-push)))
         (dynamic-wind
           (lambda () #f)
           (lambda () body ...)
           (lambda () (pool-pop pool))))]))

  ;; ============================================================
  ;; Public API - Memory Management
  ;; ============================================================

  (define (objc-retain obj)
    "Retain an Objective-C object (increment ref count)."
    (%retain obj))

  (define (objc-release obj)
    "Release an Objective-C object (decrement ref count)."
    (%release obj))

  ;; ============================================================
  ;; Public API - Runtime Class Creation
  ;; ============================================================

  (define (objc-create-class name superclass-name)
    "Create a new Objective-C class at runtime.
     Returns class pointer.  Add methods before registering.

     (define my-cls (objc-create-class \"MyDelegate\" \"NSObject\"))"
    (let ((cls (%create-class name superclass-name)))
      (when (objc-null? cls)
        (error 'objc-create-class
               "Failed to create class (name taken or superclass not found)"
               name superclass-name))
      cls))

  (define (objc-add-method! cls sel-name proc types)
    "Add a method to a class (before registration).

     cls: class from objc-create-class
     sel-name: selector string
     proc: Chez foreign-callable code object
     types: ObjC type encoding (\"v@:\" = void(id,SEL), \"v@:@\" = void(id,SEL,id))

     The proc must be created with foreign-callable and locked:
       (define cb (foreign-callable (lambda (self cmd) ...) (void* void*) void))
       (lock-object cb)
       (objc-add-method! cls \"doSomething\" cb \"v@:\")

     Common type encodings:
       v = void    @ = id (object)    : = SEL
       q = int64   d = double         B = BOOL
       \"v@:\"  = -(void)method
       \"v@:@\" = -(void)method:(id)arg
       \"@@:\"  = -(id)method
       \"@@:@\" = -(id)method:(id)arg"
    (let ((result (%add-method cls (objc-sel sel-name) proc types)))
      (when (zero? result)
        (error 'objc-add-method! "Failed to add method" sel-name))))

  (define (objc-add-ivar! cls name size alignment types)
    "Add an instance variable to a class (before registration).

     (objc-add-ivar! cls \"_handler\" 8 3 \"^v\")  ; pointer-sized"
    (let ((result (%add-ivar cls name size alignment types)))
      (when (zero? result)
        (error 'objc-add-ivar! "Failed to add ivar" name))))

  (define (objc-register-class! cls)
    "Register a dynamically-created class.  After this, instances
     can be allocated and the class is visible to the runtime."
    (%register cls))

  ;; ============================================================
  ;; Public API - Ivar Access
  ;; ============================================================

  (define (objc-set-ivar! obj name value)
    "Set an instance variable on a dynamic class instance."
    (%set-ivar obj name value))

  (define (objc-get-ivar obj name)
    "Get an instance variable from a dynamic class instance."
    (%get-ivar obj name))

  ;; ============================================================
  ;; Public API - Introspection
  ;; ============================================================

  (define (objc-class-name obj)
    "Get the class name of an Objective-C object."
    (%class-name obj))

  (define (objc-responds-to? obj sel-name)
    "Check if an object responds to a selector."
    (not (zero? (%responds-to obj (objc-sel sel-name)))))

  (define (objc-is-kind-of? obj class-name)
    "Check if an object is an instance of a class (or subclass)."
    (not (zero? (%is-kind-of obj (objc-class class-name)))))

  (define (objc-description obj)
    "Get the -description of an Objective-C object (like NSLog %@)."
    (%description obj))

  ;; ============================================================
  ;; Public API - NSApplication
  ;; ============================================================

  (define (nsapp)
    "Get or create the shared NSApplication instance."
    (%nsapp))

  (define (nsapp-set-policy! policy)
    "Set app activation policy: 'regular, 'accessory, or 'prohibited."
    (%nsapp-policy
     (case policy
       [(regular) 0]
       [(accessory) 1]
       [(prohibited) 2]
       [else (error 'nsapp-set-policy! "Unknown policy" policy)])))

  (define (nsapp-activate!)
    "Activate the application (bring to front)."
    (%nsapp-activate))

  (define (nsapp-run!)
    "Run the main event loop.  BLOCKS until app terminates."
    (%nsapp-run))

  (define (nsapp-terminate!)
    "Terminate the application."
    (%nsapp-term))

) ;; end library
