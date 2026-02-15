/*
 * Cyberspace.app - Native macOS Terminal
 * Library of Cyberspace
 *
 * Native terminal emulator using PTY connection to Chez Scheme REPL.
 * No WebView, no HTTP, no WebSocket - just Unix pipes and terminal I/O.
 *
 * Architecture: NSTextView → PTY → Chez REPL process
 */

#import <Cocoa/Cocoa.h>

// ============================================================================
// ANSITextView - NSTextView with ANSI escape sequence support
// ============================================================================

@interface ANSITextView : NSTextView
@property (nonatomic, weak) id inputHandler;
- (void)appendString:(NSString *)string;
- (void)appendANSI:(NSString *)ansiString;
@end

@implementation ANSITextView

- (instancetype)initWithFrame:(NSRect)frame {
    self = [super initWithFrame:frame];
    if (self) {
        self.editable = NO;
        self.selectable = YES;
        self.font = [NSFont fontWithName:@"SF Mono" size:13.0];
        self.backgroundColor = [NSColor colorWithRed:0.04 green:0.04 blue:0.04 alpha:1.0];
        self.textColor = [NSColor colorWithRed:0.2 green:1.0 blue:0.2 alpha:1.0];
        self.insertionPointColor = [NSColor colorWithRed:0.2 green:1.0 blue:0.2 alpha:1.0];
        [self setRichText:YES];
        [self setUsesFontPanel:NO];
    }
    return self;
}

- (void)appendString:(NSString *)string {
    NSAttributedString *attrStr = [[NSAttributedString alloc]
        initWithString:string
        attributes:@{
            NSFontAttributeName: self.font,
            NSForegroundColorAttributeName: self.textColor
        }];

    [[self textStorage] appendAttributedString:attrStr];
    [self scrollToEndOfDocument:nil];
}

- (void)appendANSI:(NSString *)ansiString {
    // Simple ANSI parsing - just strip escape codes for now
    // TODO: Implement full ANSI color support
    NSString *stripped = [ansiString stringByReplacingOccurrencesOfString:@"\x1b\\[[0-9;]*m"
                                                               withString:@""
                                                                  options:NSRegularExpressionSearch
                                                                    range:NSMakeRange(0, ansiString.length)];
    [self appendString:stripped];
}

- (void)keyDown:(NSEvent *)event {
    if ([self.inputHandler respondsToSelector:@selector(handleKeyDown:)]) {
        [self.inputHandler performSelector:@selector(handleKeyDown:) withObject:event];
    } else {
        [super keyDown:event];
    }
}

@end

// ============================================================================
// AppDelegate - Main Application
// ============================================================================

@interface AppDelegate : NSObject <NSApplicationDelegate, NSWindowDelegate, NSTextViewDelegate>
@property (nonatomic, strong) NSWindow *window;
@property (nonatomic, strong) ANSITextView *terminalView;
@property (nonatomic, strong) NSScrollView *scrollView;
@property (nonatomic, assign) int masterFD;
@property (nonatomic, assign) pid_t childPID;
@property (nonatomic, strong) NSFileHandle *masterHandle;
@property (nonatomic, strong) NSFileHandle *inputHandle;
@property (nonatomic, strong) NSMutableString *inputBuffer;
@property (nonatomic, strong) NSTask *replTask;
@end

@implementation AppDelegate

- (void)applicationDidFinishLaunching:(NSNotification *)notification {
    self.inputBuffer = [NSMutableString string];

    // Create window
    NSRect frame = NSMakeRect(100, 100, 1000, 700);
    NSWindowStyleMask style = NSWindowStyleMaskTitled |
                              NSWindowStyleMaskClosable |
                              NSWindowStyleMaskMiniaturizable |
                              NSWindowStyleMaskResizable;

    self.window = [[NSWindow alloc] initWithContentRect:frame
                                              styleMask:style
                                                backing:NSBackingStoreBuffered
                                                  defer:NO];
    self.window.title = @"Cyberspace";
    self.window.delegate = self;
    self.window.minSize = NSMakeSize(600, 400);

    // Create terminal view
    self.scrollView = [[NSScrollView alloc] initWithFrame:self.window.contentView.bounds];
    self.scrollView.hasVerticalScroller = YES;
    self.scrollView.autohidesScrollers = YES;
    self.scrollView.autoresizingMask = NSViewWidthSizable | NSViewHeightSizable;

    NSSize contentSize = [self.scrollView contentSize];
    self.terminalView = [[ANSITextView alloc] initWithFrame:NSMakeRect(0, 0, contentSize.width, contentSize.height)];
    self.terminalView.minSize = NSMakeSize(0, contentSize.height);
    self.terminalView.maxSize = NSMakeSize(FLT_MAX, FLT_MAX);
    self.terminalView.verticallyResizable = YES;
    self.terminalView.horizontallyResizable = NO;
    self.terminalView.autoresizingMask = NSViewWidthSizable;
    self.terminalView.textContainer.containerSize = NSMakeSize(contentSize.width, FLT_MAX);
    self.terminalView.textContainer.widthTracksTextView = YES;
    self.terminalView.delegate = self;

    self.scrollView.documentView = self.terminalView;
    [self.window.contentView addSubview:self.scrollView];

    // Connect input handler
    self.terminalView.inputHandler = self;

    // Set up menu (programmatic, no NIB)
    [self setupMenu];

    // Activate and show window
    [NSApp activateIgnoringOtherApps:YES];
    [self.window makeKeyAndOrderFront:nil];
    [self.window makeFirstResponder:self.terminalView];

    // Banner
    [self.terminalView appendString:@"═══════════════════════════════════════════════\n"];
    [self.terminalView appendString:@"  Cyberspace - Native macOS Terminal\n"];
    [self.terminalView appendString:@"═══════════════════════════════════════════════\n\n"];

    // Start REPL (async via NSPipe - does not block UI)
    [self startREPL];
}

- (void)startREPL {
    NSString *csScript = @"/Users/ddp/cyberspace/spki/scheme/chicken/cs";
    NSFileManager *fm = [NSFileManager defaultManager];

    // Verify binary exists
    if (![fm fileExistsAtPath:csScript]) {
        NSString *msg = [NSString stringWithFormat:@"❌ REPL binary not found\n\nExpected: %@\n", csScript];
        [self.terminalView appendString:msg];

        NSAlert *alert = [[NSAlert alloc] init];
        alert.messageText = @"REPL Not Found";
        alert.informativeText = msg;
        [alert runModal];
        return;
    }

    // Check if executable
    if (![fm isExecutableFileAtPath:csScript]) {
        NSString *msg = @"❌ REPL binary not executable\n\nRun: chmod +x cs\n";
        [self.terminalView appendString:msg];

        NSAlert *alert = [[NSAlert alloc] init];
        alert.messageText = @"REPL Not Executable";
        alert.informativeText = msg;
        [alert runModal];
        return;
    }

    [self.terminalView appendString:@"🚀 Launching Cyberspace REPL...\n\n"];
    [self.terminalView appendString:[NSString stringWithFormat:@"Binary: %@\n", csScript]];
    [self.terminalView appendString:@"Args: --boot=gate\n"];
    [self.terminalView appendString:@"Working dir: /Users/ddp/cyberspace/spki/scheme/chicken\n\n"];

    NSTask *task = [[NSTask alloc] init];
    [task setLaunchPath:csScript];
    [task setArguments:@[@"--boot=gate"]];
    [task setCurrentDirectoryPath:@"/Users/ddp/cyberspace/spki/scheme/chicken"];

    // Set up environment
    NSMutableDictionary *env = [[NSProcessInfo processInfo].environment mutableCopy];
    env[@"TERM"] = @"xterm-256color";
    env[@"CYBERSPACE_APP"] = @"1";
    task.environment = env;

    // Create pipes
    NSPipe *inputPipe = [NSPipe pipe];
    NSPipe *outputPipe = [NSPipe pipe];
    NSPipe *errorPipe = [NSPipe pipe];

    task.standardInput = inputPipe;
    task.standardOutput = outputPipe;
    task.standardError = errorPipe;

    self.masterHandle = outputPipe.fileHandleForReading;

    // Set up output reading
    [[NSNotificationCenter defaultCenter] addObserver:self
                                             selector:@selector(dataAvailable:)
                                                 name:NSFileHandleReadCompletionNotification
                                               object:self.masterHandle];
    [self.masterHandle readInBackgroundAndNotify];

    // Set up error reading
    [[NSNotificationCenter defaultCenter] addObserver:self
                                             selector:@selector(errorDataAvailable:)
                                                 name:NSFileHandleReadCompletionNotification
                                               object:errorPipe.fileHandleForReading];
    [errorPipe.fileHandleForReading readInBackgroundAndNotify];

    // Set up termination handler
    task.terminationHandler = ^(NSTask *t) {
        dispatch_async(dispatch_get_main_queue(), ^{
            NSString *msg = [NSString stringWithFormat:@"\n\n❌ REPL exited with code %d\n", t.terminationStatus];
            [self.terminalView appendString:msg];
        });
    };

    // Launch
    @try {
        [task launch];
        self.replTask = task;
        self.childPID = task.processIdentifier;
        self.inputHandle = inputPipe.fileHandleForWriting;

        NSString *msg = [NSString stringWithFormat:@"✓ REPL started (PID %d)\n\n", self.childPID];
        [self.terminalView appendString:msg];
        NSLog(@"[Cyberspace] Started cs REPL (PID %d)", self.childPID);

    } @catch (NSException *e) {
        NSString *msg = [NSString stringWithFormat:@"❌ Launch failed: %@\n\n", e.reason];
        [self.terminalView appendString:msg];

        NSAlert *alert = [[NSAlert alloc] init];
        alert.messageText = @"Failed to Launch REPL";
        alert.informativeText = e.reason;
        [alert runModal];
    }
}

- (void)dataAvailable:(NSNotification *)notification {
    NSData *data = notification.userInfo[NSFileHandleNotificationDataItem];
    if (data && data.length > 0) {
        NSString *output = [[NSString alloc] initWithData:data encoding:NSUTF8StringEncoding];
        if (output) {
            dispatch_async(dispatch_get_main_queue(), ^{
                [self.terminalView appendANSI:output];
            });
        }
        [self.masterHandle readInBackgroundAndNotify];
    }
}

- (void)errorDataAvailable:(NSNotification *)notification {
    NSData *data = notification.userInfo[NSFileHandleNotificationDataItem];
    if (data && data.length > 0) {
        NSString *output = [[NSString alloc] initWithData:data encoding:NSUTF8StringEncoding];
        if (output) {
            dispatch_async(dispatch_get_main_queue(), ^{
                [self.terminalView appendString:output];
            });
        }
        NSFileHandle *handle = [notification object];
        [handle readInBackgroundAndNotify];
    }
}

- (void)handleKeyDown:(NSEvent *)event {
    NSString *chars = event.characters;
    if (!chars || chars.length == 0) {
        return;
    }

    // Handle special keys
    if (event.keyCode == 36) { // Return
        [self.inputBuffer appendString:@"\r"];
        [self sendInput:self.inputBuffer];
        self.inputBuffer = [NSMutableString string];
    } else if (event.keyCode == 51) { // Delete
        if (self.inputBuffer.length > 0) {
            [self.inputBuffer deleteCharactersInRange:NSMakeRange(self.inputBuffer.length - 1, 1)];
            [self sendInput:@"\x7f"]; // DEL
        }
    } else if (event.keyCode == 53) { // Escape
        [self sendInput:@"\x1b"];
    } else if (event.modifierFlags & NSEventModifierFlagControl) {
        // Control characters
        unichar c = [chars characterAtIndex:0];
        if (c >= 'a' && c <= 'z') {
            char ctrl = c - 'a' + 1;
            [self sendInput:[NSString stringWithFormat:@"%c", ctrl]];
        } else if (c == 'c' || c == 'C') {
            [self sendInput:@"\x03"]; // ^C
        } else if (c == 'd' || c == 'D') {
            [self sendInput:@"\x04"]; // ^D
        }
    } else {
        [self.inputBuffer appendString:chars];
        [self sendInput:chars];
    }
}

- (void)sendInput:(NSString *)input {
    if (self.inputHandle) {
        NSData *data = [input dataUsingEncoding:NSUTF8StringEncoding];
        @try {
            [self.inputHandle writeData:data];
        } @catch (NSException *e) {
            NSLog(@"[Cyberspace] Failed to write input: %@", e);
        }
    }
}

- (void)setupMenu {
    NSMenu *menuBar = [[NSMenu alloc] init];

    // Application menu
    NSMenuItem *appMenuItem = [[NSMenuItem alloc] init];
    NSMenu *appMenu = [[NSMenu alloc] initWithTitle:@"Cyberspace"];

    [appMenu addItemWithTitle:@"About Cyberspace"
                       action:@selector(showAbout:)
                keyEquivalent:@""];
    [appMenu addItem:[NSMenuItem separatorItem]];
    [appMenu addItemWithTitle:@"Quit Cyberspace"
                       action:@selector(terminate:)
                keyEquivalent:@"q"];

    appMenuItem.submenu = appMenu;
    [menuBar addItem:appMenuItem];

    // Edit menu
    NSMenuItem *editMenuItem = [[NSMenuItem alloc] init];
    NSMenu *editMenu = [[NSMenu alloc] initWithTitle:@"Edit"];

    [editMenu addItemWithTitle:@"Copy" action:@selector(copy:) keyEquivalent:@"c"];
    [editMenu addItemWithTitle:@"Paste" action:@selector(paste:) keyEquivalent:@"v"];
    [editMenu addItemWithTitle:@"Select All" action:@selector(selectAll:) keyEquivalent:@"a"];

    editMenuItem.submenu = editMenu;
    [menuBar addItem:editMenuItem];

    [NSApp setMainMenu:menuBar];
}

- (void)showAbout:(id)sender {
    NSAlert *alert = [[NSAlert alloc] init];
    alert.messageText = @"Cyberspace";
    alert.informativeText = @"Native Scheme REPL\n\n"
                           @"PTY-based terminal with direct connection\n"
                           @"to Chez Scheme. No WebView, no WebSocket.\n\n"
                           @"Copyright 2026 Yoyodyne";
    [alert runModal];
}

- (BOOL)applicationShouldTerminateAfterLastWindowClosed:(NSApplication *)sender {
    return YES;
}

- (void)applicationWillTerminate:(NSNotification *)notification {
    if (self.replTask && self.replTask.isRunning) {
        [self.replTask terminate];
    }
}

- (void)windowWillClose:(NSNotification *)notification {
    [NSApp terminate:nil];
}

@end

// ============================================================================
// Main
// ============================================================================

int main(int argc, const char *argv[]) {
    @autoreleasepool {
        NSApplication *app = [NSApplication sharedApplication];
        [app setActivationPolicy:NSApplicationActivationPolicyRegular];

        AppDelegate *delegate = [[AppDelegate alloc] init];
        app.delegate = delegate;

        [app run];
    }
    return 0;
}
