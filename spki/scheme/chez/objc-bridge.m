/*
 * objc-bridge.m - Chez Scheme Objective-C Runtime Bridge
 * Library of Cyberspace - Chez Port
 *
 * Provides C-callable wrappers around Objective-C runtime functions
 * for use with Chez Scheme's foreign-procedure FFI.
 *
 * Why this exists: Chicken Scheme compiles to C, so you get Objective-C
 * interop for free via foreign-declare/foreign-lambda.  Chez compiles to
 * native code and can only call C functions.  This shim presents the
 * Objective-C runtime as a clean C interface that Chez can drive.
 *
 * The key problem: objc_msgSend is a variadic trampoline whose actual
 * calling convention depends on the return type and argument types of
 * the target method.  You MUST cast it to the correct function pointer
 * type before calling.  These wrappers do exactly that.
 *
 * Architecture notes:
 *   ARM64: Only objc_msgSend needed (no _stret, no _fpret)
 *   x86_64: Need objc_msgSend_fpret for double returns,
 *           objc_msgSend_stret for large struct returns
 *
 * Build: clang -shared -fobjc-arc -framework Foundation -framework Cocoa \
 *        -o libobjc-bridge.dylib objc-bridge.m
 *
 * Copyright (c) 2026 Yoyodyne. See LICENSE.
 */

#import <objc/runtime.h>
#import <objc/message.h>
#import <Foundation/Foundation.h>

/* Suppress clang's objc_msgSend type-safety warnings -- we know
   what we're doing with these casts, that's the whole point. */
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wundeclared-selector"

/* ================================================================
 * Class & Selector Lookup
 * ================================================================ */

/* Look up an Objective-C class by name.
   Returns NULL if class not found. */
void *bridge_class(const char *name) {
    return (__bridge void *)objc_getClass(name);
}

/* Register (or look up) a selector by name.
   Selectors are interned -- same string always returns same SEL. */
void *bridge_sel(const char *name) {
    return (void *)sel_registerName(name);
}

/* ================================================================
 * Alloc & Init
 * ================================================================ */

/* Send +alloc to a class.  Returns uninitialized instance. */
void *bridge_alloc(void *cls) {
    return (__bridge_retained void *)
        [(__bridge Class)cls alloc];
}

/* Send -init to an object.  Returns initialized instance.
   The init family can return a DIFFERENT object (class clusters),
   so always use the return value. */
void *bridge_init(void *obj) {
    return (__bridge_retained void *)
        [(__bridge_transfer id)obj init];
}

/* ================================================================
 * Message Send - Pointer/Object Return
 *
 * These return id (void*) -- use for methods that return objects,
 * Class, SEL, or any pointer type.
 * ================================================================ */

void *bridge_send(void *obj, void *sel) {
    return (__bridge void *)
        ((id (*)(id, SEL))objc_msgSend)
            ((__bridge id)obj, (SEL)sel);
}

void *bridge_send_1(void *obj, void *sel, void *a1) {
    return (__bridge void *)
        ((id (*)(id, SEL, id))objc_msgSend)
            ((__bridge id)obj, (SEL)sel, (__bridge id)a1);
}

void *bridge_send_2(void *obj, void *sel, void *a1, void *a2) {
    return (__bridge void *)
        ((id (*)(id, SEL, id, id))objc_msgSend)
            ((__bridge id)obj, (SEL)sel,
             (__bridge id)a1, (__bridge id)a2);
}

void *bridge_send_3(void *obj, void *sel, void *a1, void *a2, void *a3) {
    return (__bridge void *)
        ((id (*)(id, SEL, id, id, id))objc_msgSend)
            ((__bridge id)obj, (SEL)sel,
             (__bridge id)a1, (__bridge id)a2, (__bridge id)a3);
}

/* ================================================================
 * Message Send - Integer Return
 *
 * Use for NSInteger, NSUInteger, BOOL (on 64-bit), enum values.
 * ================================================================ */

long bridge_send_int(void *obj, void *sel) {
    return ((long (*)(id, SEL))objc_msgSend)
        ((__bridge id)obj, (SEL)sel);
}

long bridge_send_int_1(void *obj, void *sel, void *a1) {
    return ((long (*)(id, SEL, id))objc_msgSend)
        ((__bridge id)obj, (SEL)sel, (__bridge id)a1);
}

long bridge_send_int_long(void *obj, void *sel, long a1) {
    return ((long (*)(id, SEL, long))objc_msgSend)
        ((__bridge id)obj, (SEL)sel, a1);
}

/* ================================================================
 * Message Send - Double Return
 *
 * x86_64: Must use objc_msgSend_fpret for floating-point returns.
 * ARM64:  Regular objc_msgSend works fine.
 * ================================================================ */

double bridge_send_double(void *obj, void *sel) {
#if defined(__x86_64__)
    return ((double (*)(id, SEL))objc_msgSend_fpret)
        ((__bridge id)obj, (SEL)sel);
#else
    return ((double (*)(id, SEL))objc_msgSend)
        ((__bridge id)obj, (SEL)sel);
#endif
}

/* ================================================================
 * Message Send - Boolean Return
 * ================================================================ */

int bridge_send_bool(void *obj, void *sel) {
    return (int)((BOOL (*)(id, SEL))objc_msgSend)
        ((__bridge id)obj, (SEL)sel);
}

int bridge_send_bool_1(void *obj, void *sel, void *a1) {
    return (int)((BOOL (*)(id, SEL, id))objc_msgSend)
        ((__bridge id)obj, (SEL)sel, (__bridge id)a1);
}

/* ================================================================
 * Message Send - Void Return
 * ================================================================ */

void bridge_send_void(void *obj, void *sel) {
    ((void (*)(id, SEL))objc_msgSend)
        ((__bridge id)obj, (SEL)sel);
}

void bridge_send_void_1(void *obj, void *sel, void *a1) {
    ((void (*)(id, SEL, id))objc_msgSend)
        ((__bridge id)obj, (SEL)sel, (__bridge id)a1);
}

void bridge_send_void_2(void *obj, void *sel, void *a1, void *a2) {
    ((void (*)(id, SEL, id, id))objc_msgSend)
        ((__bridge id)obj, (SEL)sel,
         (__bridge id)a1, (__bridge id)a2);
}

void bridge_send_void_int(void *obj, void *sel, long a1) {
    ((void (*)(id, SEL, long))objc_msgSend)
        ((__bridge id)obj, (SEL)sel, a1);
}

void bridge_send_void_double(void *obj, void *sel, double a1) {
    ((void (*)(id, SEL, double))objc_msgSend)
        ((__bridge id)obj, (SEL)sel, a1);
}

void bridge_send_void_bool(void *obj, void *sel, BOOL a1) {
    ((void (*)(id, SEL, BOOL))objc_msgSend)
        ((__bridge id)obj, (SEL)sel, a1);
}

/* ================================================================
 * Message Send - CGRect/NSRect arguments
 *
 * Essential for window/view geometry.
 * NSRect = CGRect = { origin: {x, y}, size: {width, height} }
 * On ARM64, 4 doubles passed in d0-d3 (32 bytes, fits in registers).
 * ================================================================ */

void *bridge_send_rect_bool(void *obj, void *sel,
                            double x, double y, double w, double h,
                            int flag) {
    NSRect rect = NSMakeRect(x, y, w, h);
    return (__bridge void *)
        ((id (*)(id, SEL, NSRect, BOOL))objc_msgSend)
            ((__bridge id)obj, (SEL)sel, rect, (BOOL)flag);
}

void bridge_send_void_rect_bool(void *obj, void *sel,
                                double x, double y, double w, double h,
                                int flag) {
    NSRect rect = NSMakeRect(x, y, w, h);
    ((void (*)(id, SEL, NSRect, BOOL))objc_msgSend)
        ((__bridge id)obj, (SEL)sel, rect, (BOOL)flag);
}

/* ================================================================
 * NSString Bridge
 *
 * Most common Cocoa type -- optimize the conversion path.
 * ================================================================ */

/* Create NSString from C string (UTF-8). */
void *bridge_nsstring(const char *str) {
    return (__bridge_retained void *)
        [NSString stringWithUTF8String:str];
}

/* Extract C string from NSString.
   Returns pointer to internal buffer -- valid until NSString is released.
   Caller should copy if needed for persistence. */
const char *bridge_nsstring_utf8(void *nsstr) {
    return [(__bridge NSString *)nsstr UTF8String];
}

/* ================================================================
 * NSNumber Bridge
 * ================================================================ */

void *bridge_nsnumber_int(long val) {
    return (__bridge_retained void *)
        [NSNumber numberWithLong:val];
}

void *bridge_nsnumber_double(double val) {
    return (__bridge_retained void *)
        [NSNumber numberWithDouble:val];
}

/* ================================================================
 * NSDictionary Bridge
 *
 * Create from parallel arrays of keys and values.
 * ================================================================ */

void *bridge_dict_create(void **keys, void **vals, long count) {
    NSMutableDictionary *dict =
        [NSMutableDictionary dictionaryWithCapacity:count];
    for (long i = 0; i < count; i++) {
        dict[(__bridge id)keys[i]] = (__bridge id)vals[i];
    }
    return (__bridge_retained void *)dict;
}

/* ================================================================
 * NSArray Bridge
 * ================================================================ */

void *bridge_array_create(void **objects, long count) {
    NSMutableArray *arr = [NSMutableArray arrayWithCapacity:count];
    for (long i = 0; i < count; i++) {
        [arr addObject:(__bridge id)objects[i]];
    }
    return (__bridge_retained void *)arr;
}

long bridge_array_count(void *arr) {
    return (long)[(__bridge NSArray *)arr count];
}

void *bridge_array_at(void *arr, long idx) {
    return (__bridge void *)[(__bridge NSArray *)arr objectAtIndex:idx];
}

/* ================================================================
 * Autorelease Pool
 *
 * Every thread that touches Cocoa needs an autorelease pool.
 * Wrap your Scheme entry points with push/pop.
 * ================================================================ */

void *bridge_pool_push(void) {
    return (__bridge_retained void *)
        [[NSAutoreleasePool alloc] init];
}

void bridge_pool_pop(void *pool) {
    (void)(__bridge_transfer NSAutoreleasePool *)pool;
}

/* ================================================================
 * Memory Management
 * ================================================================ */

/* Explicitly retain an object (increment reference count).
   Use when Scheme needs to hold a reference. */
void *bridge_retain(void *obj) {
    return (__bridge_retained void *)
        (__bridge_transfer id)obj;
}

/* Explicitly release an object (decrement reference count).
   Object may be deallocated if count reaches zero. */
void bridge_release(void *obj) {
    (void)(__bridge_transfer id)obj;
}

/* ================================================================
 * Runtime Class Creation
 *
 * Create new Objective-C classes at runtime.  Essential for
 * implementing delegates and callback protocols from Scheme.
 *
 * Pattern:
 *   1. bridge_create_class("MyDelegate", "NSObject")
 *   2. bridge_add_method(cls, sel, imp, "v@:@")
 *   3. bridge_register_class(cls)
 *   4. bridge_alloc + bridge_init
 * ================================================================ */

/* Create a new class pair (class + metaclass).
   Returns the new class, or NULL if name already exists. */
void *bridge_create_class(const char *name, const char *superclass_name) {
    Class super = objc_getClass(superclass_name);
    if (!super) return NULL;
    Class cls = objc_allocateClassPair(super, name, 0);
    return (__bridge void *)cls;
}

/* Add a method to a class (must be done BEFORE registering).
   imp: function pointer (from Chez foreign-callable)
   types: Objective-C type encoding string
          "v@:" = void return, id self, SEL _cmd
          "v@:@" = void return, id self, SEL _cmd, id arg1
          "@@:" = id return, id self, SEL _cmd
   Returns 1 on success, 0 on failure. */
int bridge_add_method(void *cls, void *sel, void *imp, const char *types) {
    return (int)class_addMethod((__bridge Class)cls,
                                (SEL)sel,
                                (IMP)imp,
                                types);
}

/* Add an ivar (instance variable) to a class.
   Must be done BEFORE registering. */
int bridge_add_ivar(void *cls, const char *name, long size,
                    unsigned char alignment, const char *types) {
    return (int)class_addIvar((__bridge Class)cls, name,
                              (size_t)size, alignment, types);
}

/* Register a dynamically-created class.  After this, it's live
   and you can alloc/init instances. */
void bridge_register_class(void *cls) {
    objc_registerClassPair((__bridge Class)cls);
}

/* ================================================================
 * Ivar Access (for dynamic classes)
 * ================================================================ */

void bridge_set_ivar_ptr(void *obj, const char *name, void *value) {
    Ivar ivar = class_getInstanceVariable(
        object_getClass((__bridge id)obj), name);
    if (ivar) {
        object_setIvar((__bridge id)obj, ivar, (__bridge id)value);
    }
}

void *bridge_get_ivar_ptr(void *obj, const char *name) {
    Ivar ivar = class_getInstanceVariable(
        object_getClass((__bridge id)obj), name);
    if (ivar) {
        return (__bridge void *)object_getIvar((__bridge id)obj, ivar);
    }
    return NULL;
}

/* ================================================================
 * Introspection
 * ================================================================ */

/* Get the class name of an object. */
const char *bridge_class_name(void *obj) {
    return class_getName(object_getClass((__bridge id)obj));
}

/* Check if an object responds to a selector. */
int bridge_responds_to(void *obj, void *sel) {
    return (int)[(__bridge id)obj respondsToSelector:(SEL)sel];
}

/* Check if an object is an instance of a class (or subclass). */
int bridge_is_kind_of(void *obj, void *cls) {
    return (int)[(__bridge id)obj isKindOfClass:(__bridge Class)cls];
}

/* Get description (like NSLog's %@). */
const char *bridge_description(void *obj) {
    return [[(__bridge id)obj description] UTF8String];
}

/* ================================================================
 * NSApplication Bootstrap
 *
 * Minimal support for creating a Cocoa app from Scheme.
 * ================================================================ */

/* Get or create the shared NSApplication instance.
   Must be called before any UI work. */
void *bridge_nsapp(void) {
    return (__bridge void *)[NSApplication sharedApplication];
}

/* Set the app activation policy.
   0 = regular (shows in Dock), 1 = accessory, 2 = prohibited */
void bridge_nsapp_set_policy(int policy) {
    [NSApp setActivationPolicy:(NSApplicationActivationPolicy)policy];
}

/* Activate the app (bring to front). */
void bridge_nsapp_activate(void) {
    [NSApp activateIgnoringOtherApps:YES];
}

/* Run the main event loop.  This BLOCKS -- call from main thread. */
void bridge_nsapp_run(void) {
    [NSApp run];
}

/* Terminate the app. */
void bridge_nsapp_terminate(void) {
    [NSApp terminate:nil];
}

#pragma clang diagnostic pop
