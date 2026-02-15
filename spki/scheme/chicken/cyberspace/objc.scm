;;; Objective-C Runtime Bridge - Chicken Scheme
;;;
;;; Chicken compiles Scheme to C via csc, so Objective-C interop
;;; is available natively through the FFI without a bridge library.
;;;
;;; This module provides the same API surface as the Chez objc.sls
;;; module, but implemented directly through Chicken's C FFI.
;;;
;;; Heritage: Chez needs libobjc-bridge.dylib because it can't
;;; compile to C.  Chicken gets ObjC for free from csc.

(module objc
  (;; Initialization
   objc-init!

   ;; Class & selector
   objc-class objc-sel

   ;; Alloc & init
   objc-alloc objc-init-obj

   ;; Message send by return type
   msg       msg/1     msg/2     msg/3
   msg/int   msg/int1  msg/int-long
   msg/double
   msg/bool  msg/bool1
   msg/void  msg/void1 msg/void2
   msg/void-int msg/void-double msg/void-bool

   ;; NSString
   nsstring nsstring->string

   ;; Autorelease pool
   with-autorelease-pool pool-push pool-pop

   ;; Memory management
   objc-retain objc-release

   ;; Null
   objc-null objc-null?)

  (import scheme
          (chicken base)
          (chicken foreign))

  ;; ============================================================
  ;; Foreign declarations
  ;; ============================================================

  (foreign-declare "
    #import <objc/runtime.h>
    #import <objc/message.h>
    #import <Foundation/Foundation.h>
  ")

  (define objc-null (foreign-value "NULL" (c-pointer void)))

  (define (objc-null? obj)
    (or (not obj) (eq? obj objc-null)))

  (define (objc-init!) (void))

  ;; Class & selector
  (define objc-class
    (foreign-lambda* (c-pointer void) ((c-string name))
      "C_return(objc_getClass(name));"))

  (define objc-sel
    (foreign-lambda* (c-pointer void) ((c-string name))
      "C_return(sel_registerName(name));"))

  ;; Alloc & init
  (define objc-alloc
    (foreign-lambda* (c-pointer void) (((c-pointer void) cls))
      "C_return(((id(*)(id,SEL))objc_msgSend)((id)cls, sel_registerName(\"alloc\")));"))

  (define objc-init-obj
    (foreign-lambda* (c-pointer void) (((c-pointer void) obj))
      "C_return(((id(*)(id,SEL))objc_msgSend)((id)obj, sel_registerName(\"init\")));"))

  ;; Message send - pointer return
  (define msg
    (foreign-lambda* (c-pointer void) (((c-pointer void) obj) ((c-pointer void) sel))
      "C_return(((id(*)(id,SEL))objc_msgSend)((id)obj, (SEL)sel));"))

  (define msg/1
    (foreign-lambda* (c-pointer void) (((c-pointer void) obj) ((c-pointer void) sel) ((c-pointer void) a))
      "C_return(((id(*)(id,SEL,id))objc_msgSend)((id)obj, (SEL)sel, (id)a));"))

  (define msg/2
    (foreign-lambda* (c-pointer void) (((c-pointer void) obj) ((c-pointer void) sel) ((c-pointer void) a) ((c-pointer void) b))
      "C_return(((id(*)(id,SEL,id,id))objc_msgSend)((id)obj, (SEL)sel, (id)a, (id)b));"))

  (define msg/3
    (foreign-lambda* (c-pointer void) (((c-pointer void) obj) ((c-pointer void) sel) ((c-pointer void) a) ((c-pointer void) b) ((c-pointer void) c))
      "C_return(((id(*)(id,SEL,id,id,id))objc_msgSend)((id)obj, (SEL)sel, (id)a, (id)b, (id)c));"))

  ;; Message send - integer return
  (define msg/int
    (foreign-lambda* long (((c-pointer void) obj) ((c-pointer void) sel))
      "C_return((long)((NSInteger(*)(id,SEL))objc_msgSend)((id)obj, (SEL)sel));"))

  (define msg/int1
    (foreign-lambda* long (((c-pointer void) obj) ((c-pointer void) sel) ((c-pointer void) a))
      "C_return((long)((NSInteger(*)(id,SEL,id))objc_msgSend)((id)obj, (SEL)sel, (id)a));"))

  (define msg/int-long
    (foreign-lambda* long (((c-pointer void) obj) ((c-pointer void) sel) (long a))
      "C_return((long)((NSInteger(*)(id,SEL,NSInteger))objc_msgSend)((id)obj, (SEL)sel, (NSInteger)a));"))

  ;; Message send - double return
  (define msg/double
    (foreign-lambda* double (((c-pointer void) obj) ((c-pointer void) sel))
      "C_return(((double(*)(id,SEL))objc_msgSend_fpret)((id)obj, (SEL)sel));"))

  ;; Message send - boolean return
  (define (msg/bool obj sel)
    (not (zero? ((foreign-lambda* int (((c-pointer void) obj) ((c-pointer void) sel))
      "C_return((int)((BOOL(*)(id,SEL))objc_msgSend)((id)obj, (SEL)sel));") obj sel))))

  (define (msg/bool1 obj sel a)
    (not (zero? ((foreign-lambda* int (((c-pointer void) obj) ((c-pointer void) sel) ((c-pointer void) a))
      "C_return((int)((BOOL(*)(id,SEL,id))objc_msgSend)((id)obj, (SEL)sel, (id)a));") obj sel a))))

  ;; Message send - void return
  (define msg/void
    (foreign-lambda* void (((c-pointer void) obj) ((c-pointer void) sel))
      "((void(*)(id,SEL))objc_msgSend)((id)obj, (SEL)sel);"))

  (define msg/void1
    (foreign-lambda* void (((c-pointer void) obj) ((c-pointer void) sel) ((c-pointer void) a))
      "((void(*)(id,SEL,id))objc_msgSend)((id)obj, (SEL)sel, (id)a);"))

  (define msg/void2
    (foreign-lambda* void (((c-pointer void) obj) ((c-pointer void) sel) ((c-pointer void) a) ((c-pointer void) b))
      "((void(*)(id,SEL,id,id))objc_msgSend)((id)obj, (SEL)sel, (id)a, (id)b);"))

  (define msg/void-int
    (foreign-lambda* void (((c-pointer void) obj) ((c-pointer void) sel) (long n))
      "((void(*)(id,SEL,NSInteger))objc_msgSend)((id)obj, (SEL)sel, (NSInteger)n);"))

  (define msg/void-double
    (foreign-lambda* void (((c-pointer void) obj) ((c-pointer void) sel) (double d))
      "((void(*)(id,SEL,double))objc_msgSend)((id)obj, (SEL)sel, d);"))

  (define msg/void-bool
    (foreign-lambda* void (((c-pointer void) obj) ((c-pointer void) sel) (bool b))
      "((void(*)(id,SEL,BOOL))objc_msgSend)((id)obj, (SEL)sel, (BOOL)b);"))

  ;; NSString
  (define nsstring
    (foreign-lambda* (c-pointer void) ((c-string str))
      "C_return((__bridge void *)[NSString stringWithUTF8String:str]);"))

  (define nsstring->string
    (foreign-lambda* c-string (((c-pointer void) nsstr))
      "C_return([(__bridge NSString *)nsstr UTF8String]);"))

  ;; Autorelease pool
  (define pool-push
    (foreign-lambda* (c-pointer void) ()
      "C_return((__bridge_retained void *)[[NSAutoreleasePool alloc] init]);"))

  (define pool-pop
    (foreign-lambda* void (((c-pointer void) pool))
      "[(__bridge_transfer NSAutoreleasePool *)pool release];"))

  (define-syntax with-autorelease-pool
    (syntax-rules ()
      [(_ body ...)
       (let ((pool (pool-push)))
         (dynamic-wind
           (lambda () #f)
           (lambda () body ...)
           (lambda () (pool-pop pool))))]))

  ;; Memory management
  (define objc-retain
    (foreign-lambda* (c-pointer void) (((c-pointer void) obj))
      "C_return((__bridge void *)(__bridge_transfer id)obj);"))

  (define objc-release
    (foreign-lambda* void (((c-pointer void) obj))
      "CFRelease(obj);"))

) ;; end module
