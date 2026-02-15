/*
 * main-native.m - Native Cyberspace REPL for macOS
 *
 * Direct Chez Scheme integration without HTTP/WebSocket server.
 * Copyright (c) 2026 Yoyodyne. See LICENSE.
 */

#import <Cocoa/Cocoa.h>
#import "scheme-bridge.h"

// Custom text view with VT220 block cursor
@interface BlockCursorTextView : NSTextView
@end

@implementation BlockCursorTextView

- (void)drawInsertionPointInRect:(NSRect)rect color:(NSColor *)color turnedOn:(BOOL)flag {
    if (flag) {
        // Draw filled block cursor (VT220 style)
        NSColor *amberColor = [NSColor colorWithRed:1.0 green:0.69 blue:0.0 alpha:0.5];
        [amberColor setFill];

        // Make it block width
        NSRect blockRect = rect;
        blockRect.size.width = [@"M" sizeWithAttributes:@{NSFontAttributeName: self.font}].width;
        NSRectFill(blockRect);
    }
}

@end

typedef NS_ENUM(NSInteger, ColorTheme) {
    ColorThemeAmber = 0,      // VT220 amber
    ColorThemeDECBlue = 1,    // DEC blue
    ColorThemeIBM3270 = 2     // IBM 3270 green
};

@interface CyberspaceNativeREPL : NSObject <NSApplicationDelegate, NSTextViewDelegate>
@property (strong) NSWindow *window;
@property (strong) BlockCursorTextView *textView;
@property (strong) NSMutableArray *history;
@property NSInteger historyIndex;
@property NSUInteger promptStart;
@property BOOL schemerMode;
@property ColorTheme theme;
@property (strong) NSWindow *preferencesWindow;
@property (strong) NSButton *fontButton;
@end

// Global reference to delegate for C bridge
static CyberspaceNativeREPL *g_delegate = nil;

@implementation CyberspaceNativeREPL

- (NSString *)historyFilePath {
    NSString *appSupport = [NSSearchPathForDirectoriesInDomains(NSApplicationSupportDirectory, NSUserDomainMask, YES) firstObject];
    NSString *cyberspaceDir = [appSupport stringByAppendingPathComponent:@"Cyberspace"];
    [[NSFileManager defaultManager] createDirectoryAtPath:cyberspaceDir withIntermediateDirectories:YES attributes:nil error:nil];
    return [cyberspaceDir stringByAppendingPathComponent:@"repl-history"];
}

- (void)loadHistory {
    NSString *historyPath = [self historyFilePath];
    if ([[NSFileManager defaultManager] fileExistsAtPath:historyPath]) {
        NSArray *savedHistory = [NSArray arrayWithContentsOfFile:historyPath];
        if (savedHistory) {
            [self.history addObjectsFromArray:savedHistory];
            self.historyIndex = self.history.count;
        }
    }
}

- (void)saveHistory {
    NSString *historyPath = [self historyFilePath];
    // Keep only last 1000 commands
    NSArray *historyToSave = self.history.count > 1000 ?
        [self.history subarrayWithRange:NSMakeRange(self.history.count - 1000, 1000)] :
        self.history;
    [historyToSave writeToFile:historyPath atomically:YES];
}

- (instancetype)init {
    self = [super init];
    if (self) {
        _history = [NSMutableArray array];
        _historyIndex = 0;
        _schemerMode = NO;  // Start in novice mode

        // Restore saved theme or default to VT220 amber
        NSInteger savedTheme = [[NSUserDefaults standardUserDefaults] integerForKey:@"ColorTheme"];
        _theme = (savedTheme >= 0 && savedTheme <= ColorThemeIBM3270) ? (ColorTheme)savedTheme : ColorThemeAmber;

        g_delegate = self;
    }
    return self;
}

- (void)applicationDidFinishLaunching:(NSNotification *)notification {
    // Set activation policy for proper app behavior
    [NSApp setActivationPolicy:NSApplicationActivationPolicyRegular];

    // Set up resource path for Scheme library loading
    NSString *resourcePath = [[NSBundle mainBundle] resourcePath];
    setenv("RESOURCEPATH", [resourcePath UTF8String], 1);
    NSLog(@"Resource path: %@", resourcePath);

    // Initialize Scheme
    NSLog(@"Initializing Scheme...");
    char *argv[] = {"cyberspace", NULL};
    if (!scheme_init(1, argv)) {
        NSLog(@"FATAL: Failed to initialize Scheme");
        NSAlert *alert = [[NSAlert alloc] init];
        alert.messageText = @"Failed to initialize Scheme";
        alert.informativeText = @"Check Console.app for errors";
        [alert runModal];
        [NSApp terminate:nil];
        return;
    }
    NSLog(@"Scheme initialized successfully");

    // Create window
    NSLog(@"Creating window...");
    NSRect frame = NSMakeRect(100, 100, 800, 600);
    self.window = [[NSWindow alloc] initWithContentRect:frame
                                              styleMask:(NSWindowStyleMaskTitled |
                                                        NSWindowStyleMaskClosable |
                                                        NSWindowStyleMaskMiniaturizable |
                                                        NSWindowStyleMaskResizable)
                                                backing:NSBackingStoreBuffered
                                                  defer:NO];
    self.window.title = @"Cyberspace";
    [self.window standardWindowButton:NSWindowCloseButton].hidden = NO;
    [self.window standardWindowButton:NSWindowMiniaturizeButton].hidden = NO;
    [self.window standardWindowButton:NSWindowZoomButton].hidden = NO;
    [self.window setFrameAutosaveName:@"CyberspaceMainWindow"];

    // Create a container view with correct bounds
    NSView *container = [[NSView alloc] initWithFrame:self.window.contentView.bounds];
    container.autoresizingMask = NSViewWidthSizable | NSViewHeightSizable;
    [self.window setContentView:container];

    container.wantsLayer = YES;
    container.layer.backgroundColor = [[self backgroundColor] CGColor];

    NSRect containerBounds = container.bounds;

    // Create single scrolling text view with inline input
    NSLog(@"Creating text view...");
    NSScrollView *scrollView = [[NSScrollView alloc] initWithFrame:containerBounds];
    scrollView.hasVerticalScroller = YES;
    scrollView.autoresizingMask = NSViewWidthSizable | NSViewHeightSizable;

    self.textView = [[BlockCursorTextView alloc] initWithFrame:scrollView.bounds];
    self.textView.editable = YES;
    self.textView.selectable = YES;
    self.textView.richText = NO;
    self.textView.backgroundColor = [self backgroundColor];
    self.textView.textColor = [self textColor];

    // Restore saved font or use default
    NSFont *savedFont = nil;
    NSData *fontData = [[NSUserDefaults standardUserDefaults] objectForKey:@"TerminalFont"];
    if (fontData) {
        savedFont = [NSUnarchiver unarchiveObjectWithData:fontData];
    }
    self.textView.font = savedFont ?: ([NSFont fontWithName:@"SF Mono" size:13] ?: [NSFont monospacedSystemFontOfSize:13 weight:NSFontWeightRegular]);

    self.textView.insertionPointColor = [self textColor];
    self.textView.delegate = self;
    self.textView.autoresizingMask = NSViewWidthSizable | NSViewHeightSizable;
    [self.textView setTypingAttributes:@{
        NSForegroundColorAttributeName: [self textColor],
        NSFontAttributeName: self.textView.font
    }];

    scrollView.documentView = self.textView;
    [container addSubview:scrollView];

    // Show banner with reverse video title (DEC Digital-style: each letter highlighted)
    NSLog(@"Adding banner text...");

    // Reverse video banner: dark text on light background, only for letters not spaces
    NSString *bannerText = @"C Y B E R S P A C E\n";
    NSMutableAttributedString *banner = [[NSMutableAttributedString alloc] initWithString:bannerText];
    [banner addAttribute:NSFontAttributeName
                   value:self.textView.font
                   range:NSMakeRange(0, banner.length)];

    // Apply reverse video to each letter individually (not spaces)
    for (NSUInteger i = 0; i < bannerText.length; i++) {
        unichar c = [bannerText characterAtIndex:i];
        if (c != ' ' && c != '\n') {
            [banner addAttribute:NSForegroundColorAttributeName
                           value:[self highlightTextColor]
                           range:NSMakeRange(i, 1)];
            [banner addAttribute:NSBackgroundColorAttributeName
                           value:[self highlightBackgroundColor]
                           range:NSMakeRange(i, 1)];
        }
    }
    [[self.textView textStorage] appendAttributedString:banner];

    [self appendText:@"Library of Cyberspace v0.9.12\n" color:[self dimTextColor]];
    [self appendText:@"Chez Scheme REPL\n\n" color:[self dimTextColor]];

    // Load command history
    [self loadHistory];

    [self showPrompt];
    NSLog(@"Prompt shown");

    // Create menu bar
    NSMenu *menubar = [[NSMenu alloc] init];
    NSMenuItem *appMenuItem = [[NSMenuItem alloc] init];
    [menubar addItem:appMenuItem];
    [NSApp setMainMenu:menubar];

    NSMenu *appMenu = [[NSMenu alloc] init];
    NSMenuItem *aboutMenuItem = [[NSMenuItem alloc] initWithTitle:@"About Cyberspace"
                                                           action:@selector(showAbout:)
                                                    keyEquivalent:@""];
    aboutMenuItem.target = self;
    [appMenu addItem:aboutMenuItem];
    [appMenu addItem:[NSMenuItem separatorItem]];

    NSMenuItem *prefsMenuItem = [[NSMenuItem alloc] initWithTitle:@"Preferences..."
                                                           action:@selector(showPreferences:)
                                                    keyEquivalent:@","];
    prefsMenuItem.target = self;
    [appMenu addItem:prefsMenuItem];
    [appMenu addItem:[NSMenuItem separatorItem]];

    NSMenuItem *quitMenuItem = [[NSMenuItem alloc] initWithTitle:@"Quit Cyberspace"
                                                          action:@selector(terminate:)
                                                   keyEquivalent:@"q"];
    [appMenu addItem:quitMenuItem];
    [appMenuItem setSubmenu:appMenu];

    // Help menu
    NSMenuItem *helpMenuItem = [[NSMenuItem alloc] init];
    [menubar addItem:helpMenuItem];
    NSMenu *helpMenu = [[NSMenu alloc] initWithTitle:@"Help"];

    NSMenuItem *helpCommandsItem = [[NSMenuItem alloc] initWithTitle:@"Available Commands"
                                                              action:@selector(showHelpCommands:)
                                                       keyEquivalent:@"?"];
    helpCommandsItem.target = self;
    [helpMenu addItem:helpCommandsItem];

    NSMenuItem *helpVaultItem = [[NSMenuItem alloc] initWithTitle:@"Vault and Storage"
                                                           action:@selector(showHelpVault:)
                                                    keyEquivalent:@""];
    helpVaultItem.target = self;
    [helpMenu addItem:helpVaultItem];

    NSMenuItem *helpRealmItem = [[NSMenuItem alloc] initWithTitle:@"Realm Status and Management"
                                                           action:@selector(showHelpRealm:)
                                                    keyEquivalent:@""];
    helpRealmItem.target = self;
    [helpMenu addItem:helpRealmItem];

    NSMenuItem *helpSPKIItem = [[NSMenuItem alloc] initWithTitle:@"SPKI Certificates and Authorization"
                                                          action:@selector(showHelpSPKI:)
                                                   keyEquivalent:@""];
    helpSPKIItem.target = self;
    [helpMenu addItem:helpSPKIItem];

    NSMenuItem *helpCryptoItem = [[NSMenuItem alloc] initWithTitle:@"Cryptographic Operations (Keygen, Sign, Verify)"
                                                            action:@selector(showHelpCrypto:)
                                                     keyEquivalent:@""];
    helpCryptoItem.target = self;
    [helpMenu addItem:helpCryptoItem];

    NSMenuItem *helpModulesItem = [[NSMenuItem alloc] initWithTitle:@"Available Modules and Libraries"
                                                             action:@selector(showHelpModules:)
                                                      keyEquivalent:@""];
    helpModulesItem.target = self;
    [helpMenu addItem:helpModulesItem];

    [helpMenuItem setSubmenu:helpMenu];

    [self.window makeKeyAndOrderFront:nil];
    [NSApp activateIgnoringOtherApps:YES];

    // Ensure text view gets focus
    dispatch_after(dispatch_time(DISPATCH_TIME_NOW, 0.1 * NSEC_PER_SEC),
                   dispatch_get_main_queue(), ^{
        [self.window makeFirstResponder:self.textView];
    });
}

- (void)appendText:(NSString *)text color:(NSColor *)color {
    @try {
        NSDictionary *attrs = @{
            NSForegroundColorAttributeName: color,
            NSFontAttributeName: self.textView.font
        };
        NSAttributedString *attrString = [[NSAttributedString alloc] initWithString:text attributes:attrs];

        NSTextStorage *storage = self.textView.textStorage;
        [storage beginEditing];
        [storage appendAttributedString:attrString];
        [storage endEditing];
        [self.textView scrollRangeToVisible:NSMakeRange(self.textView.string.length, 0)];
    } @catch (NSException *e) {
        NSLog(@"appendText error: %@", e);
    }
}

- (NSColor *)backgroundColor {
    if (self.theme == ColorThemeDECBlue) {
        return [NSColor colorWithRed:0.0 green:0.02 blue:0.08 alpha:1.0];  // DEC dark blue-black
    } else if (self.theme == ColorThemeIBM3270) {
        return [NSColor colorWithRed:0.0 green:0.02 blue:0.0 alpha:1.0];   // Dark green-black
    } else {
        return [NSColor colorWithRed:0.04 green:0.04 blue:0.04 alpha:1.0]; // VT220 black
    }
}

- (NSColor *)textColor {
    if (self.theme == ColorThemeDECBlue) {
        return [NSColor colorWithRed:0.4 green:0.85 blue:1.0 alpha:1.0];   // DEC cyan
    } else if (self.theme == ColorThemeIBM3270) {
        return [NSColor colorWithRed:0.3 green:1.0 blue:0.3 alpha:1.0];    // IBM 3270 green
    } else {
        return [NSColor colorWithRed:1.0 green:0.69 blue:0.0 alpha:1.0];   // VT220 amber
    }
}

- (NSColor *)highlightTextColor {
    if (self.theme == ColorThemeDECBlue) {
        return [NSColor colorWithRed:0.0 green:0.05 blue:0.15 alpha:1.0];  // Dark blue for DEC reverse
    } else if (self.theme == ColorThemeIBM3270) {
        return [NSColor colorWithRed:0.0 green:0.08 blue:0.0 alpha:1.0];   // Dark green for IBM reverse
    } else {
        return [NSColor colorWithRed:0.04 green:0.04 blue:0.04 alpha:1.0]; // Dark for amber reverse
    }
}

- (NSColor *)highlightBackgroundColor {
    if (self.theme == ColorThemeDECBlue) {
        return [NSColor colorWithRed:0.4 green:0.85 blue:1.0 alpha:1.0];   // DEC cyan background
    } else if (self.theme == ColorThemeIBM3270) {
        return [NSColor colorWithRed:0.3 green:1.0 blue:0.3 alpha:1.0];    // IBM 3270 green background
    } else {
        return [NSColor colorWithRed:1.0 green:0.78 blue:0.25 alpha:1.0];  // Amber background
    }
}

- (NSColor *)dimTextColor {
    if (self.theme == ColorThemeDECBlue) {
        return [NSColor colorWithRed:0.3 green:0.6 blue:0.75 alpha:1.0];   // Dimmer cyan
    } else if (self.theme == ColorThemeIBM3270) {
        return [NSColor colorWithRed:0.2 green:0.7 blue:0.2 alpha:1.0];    // Dimmer green
    } else {
        return [NSColor colorWithRed:0.8 green:0.55 blue:0.0 alpha:1.0];   // Dimmer amber
    }
}

- (NSColor *)errorColor {
    if (self.theme == ColorThemeDECBlue) {
        return [NSColor colorWithRed:1.0 green:0.4 blue:0.5 alpha:1.0];    // Pink-red for DEC
    } else if (self.theme == ColorThemeIBM3270) {
        return [NSColor colorWithRed:1.0 green:0.5 blue:0.3 alpha:1.0];    // Orange-red for IBM
    } else {
        return [NSColor colorWithRed:1.0 green:0.3 blue:0.3 alpha:1.0];    // Red for amber
    }
}

- (NSString *)praharNameForHour:(NSInteger)hour {
    if (hour >= 4 && hour < 6) return @"brahma muhūrta (ब्रह्म मुहूर्त)";
    if (hour >= 6 && hour < 8) return @"prātaḥkāla (प्रातःकाल)";
    if (hour >= 8 && hour < 11) return @"saṅgava (सङ्गव)";
    if (hour >= 11 && hour < 14) return @"madhyāhna (मध्याह्न)";
    if (hour >= 14 && hour < 17) return @"aparāhṇa (अपराह्ण)";
    if (hour >= 17 && hour < 19) return @"sāyāhna (सायाह्न)";
    if (hour >= 19 && hour < 22) return @"pradoṣa (प्रदोष)";
    return @"niśītha (निशीथ)";
}

- (NSColor *)ragaColorForHour:(NSInteger)hour {
    // Raga colors based on prahar (watches)
    if (hour >= 4 && hour < 6) return [NSColor colorWithRed:0.58 green:0.44 blue:0.86 alpha:1.0];  // violet
    if (hour >= 6 && hour < 8) return [NSColor colorWithRed:1.0 green:0.84 blue:0.0 alpha:1.0];    // gold
    if (hour >= 8 && hour < 11) return [NSColor colorWithRed:0.0 green:0.5 blue:0.5 alpha:1.0];    // teal
    if (hour >= 11 && hour < 14) return [NSColor colorWithRed:0.6 green:1.0 blue:0.6 alpha:1.0];   // phosphor
    if (hour >= 14 && hour < 17) return [NSColor colorWithRed:0.4 green:1.0 blue:0.4 alpha:1.0];   // neon
    if (hour >= 17 && hour < 19) return [NSColor colorWithRed:1.0 green:0.65 blue:0.0 alpha:1.0];  // orange
    if (hour >= 19 && hour < 22) return [NSColor colorWithRed:1.0 green:0.5 blue:0.31 alpha:1.0];  // coral
    return [NSColor colorWithRed:0.0 green:1.0 blue:1.0 alpha:1.0];                                 // cyan (night)
}

- (void)showPrompt {
    NSString *prompt = self.schemerMode ? @"λ " : @"% ";

    // Get current hour for raga color
    NSCalendar *calendar = [NSCalendar currentCalendar];
    NSDateComponents *components = [calendar components:NSCalendarUnitHour fromDate:[NSDate date]];
    NSInteger hour = components.hour;

    // Use raga color for lambda, dim theme color for novice prompt
    NSColor *promptColor = self.schemerMode ?
        [self ragaColorForHour:hour] :
        [self dimTextColor];

    [self appendText:prompt color:promptColor];
    self.promptStart = self.textView.string.length;

    // Move cursor to end
    [self.textView setSelectedRange:NSMakeRange(self.textView.string.length, 0)];
}

- (void)handleInput {
    NSString *fullText = self.textView.string;
    if (self.promptStart >= fullText.length) return;

    NSString *input = [fullText substringFromIndex:self.promptStart];
    if (input.length == 0) return;

    // Add to history and save immediately
    [self.history addObject:input];
    self.historyIndex = self.history.count;
    [self saveHistory];

    // Add newline after input
    [self appendText:@"\n" color:self.textView.textColor];

    // Auto-switch to schemer mode if input starts with ( or ,
    NSString *trimmed = [input stringByTrimmingCharactersInSet:[NSCharacterSet whitespaceCharacterSet]];
    if ([trimmed hasPrefix:@"("] || [trimmed hasPrefix:@","]) {
        self.schemerMode = YES;
    }

    // Check for explicit mode switching commands
    if ([trimmed isEqualToString:@"(novice)"]) {
        self.schemerMode = NO;
        [self appendText:@"Switched to novice mode\n" color:self.textView.textColor];
    } else if ([trimmed isEqualToString:@"(schemer)"]) {
        self.schemerMode = YES;
        [self appendText:@"Switched to schemer mode\n" color:self.textView.textColor];
    } else if (self.schemerMode) {
        // Schemer mode: evaluate Scheme
        char *result = scheme_eval([input UTF8String]);
        if (result) {
            NSString *resultStr = [NSString stringWithUTF8String:result];
            NSColor *resultColor = [resultStr hasPrefix:@"Error"] ?
                [self errorColor] :
                [self textColor];
            [self appendText:resultStr color:resultColor];
            [self appendText:@"\n" color:resultColor];
            scheme_free_result(result);
        }
    } else {
        // Novice mode: handle English commands
        [self handleNoviceCommand:input];
    }

    // Show new prompt
    [self showPrompt];
}

- (void)handleNoviceCommand:(NSString *)input {
    NSString *cmd = [input stringByTrimmingCharactersInSet:[NSCharacterSet whitespaceCharacterSet]];

    if ([cmd isEqualToString:@"help"]) {
        [self appendText:@"Available commands:\n" color:self.textView.textColor];
        [self appendText:@"  help              - Show this message\n" color:self.textView.textColor];
        [self appendText:@"  describe <thing>  - Explain what something is\n" color:self.textView.textColor];
        [self appendText:@"  inspect <thing>   - Show contents\n" color:self.textView.textColor];
        [self appendText:@"\nTry: describe scheme\n" color:[NSColor colorWithRed:0.8 green:0.55 blue:0.0 alpha:1.0]];
    } else if ([cmd hasPrefix:@"describe "]) {
        NSString *thing = [[cmd substringFromIndex:9] stringByTrimmingCharactersInSet:[NSCharacterSet whitespaceCharacterSet]];
        if ([thing isEqualToString:@"scheme"]) {
            [self appendText:@"Everything here is Scheme underneath.\n" color:self.textView.textColor];
            [self appendText:@"The : prompt accepts commands. Parentheses unlock the language.\n" color:self.textView.textColor];
            [self appendText:@"Try: (+ 1 2) or (help)\n" color:[NSColor colorWithRed:0.8 green:0.55 blue:0.0 alpha:1.0]];
        } else {
            [self appendText:[NSString stringWithFormat:@"Unknown: %@\n", thing] color:self.textView.textColor];
        }
    } else if ([cmd hasPrefix:@"inspect "]) {
        [self appendText:@"Inspector not yet implemented\n" color:self.textView.textColor];
    } else {
        [self appendText:[NSString stringWithFormat:@"Unknown command: %@\nTry 'help'\n", cmd] color:self.textView.textColor];
    }
}

- (BOOL)textView:(NSTextView *)textView doCommandBySelector:(SEL)commandSelector {
    // Handle Enter key
    if (commandSelector == @selector(insertNewline:)) {
        [self handleInput];
        return YES;
    }

    // Handle arrow keys for history
    if (commandSelector == @selector(moveUp:)) {
        if (self.historyIndex > 0) {
            self.historyIndex--;
            // Replace current input with history
            NSRange inputRange = NSMakeRange(self.promptStart, self.textView.string.length - self.promptStart);
            [self.textView replaceCharactersInRange:inputRange withString:self.history[self.historyIndex]];
        }
        return YES;
    } else if (commandSelector == @selector(moveDown:)) {
        if (self.historyIndex < self.history.count - 1) {
            self.historyIndex++;
            NSRange inputRange = NSMakeRange(self.promptStart, self.textView.string.length - self.promptStart);
            [self.textView replaceCharactersInRange:inputRange withString:self.history[self.historyIndex]];
        } else {
            self.historyIndex = self.history.count;
            NSRange inputRange = NSMakeRange(self.promptStart, self.textView.string.length - self.promptStart);
            [self.textView replaceCharactersInRange:inputRange withString:@""];
        }
        return YES;
    }
    return NO;
}

- (BOOL)textView:(NSTextView *)textView shouldChangeTextInRange:(NSRange)affectedCharRange replacementString:(NSString *)replacementString {
    // Prevent editing before the prompt
    if (affectedCharRange.location < self.promptStart) {
        return NO;
    }
    return YES;
}

- (void)showPreferences:(id)sender {
    // Close existing preferences window if open
    if (self.preferencesWindow) {
        [self.preferencesWindow close];
    }

    // Create preferences window
    self.preferencesWindow = [[NSWindow alloc] initWithContentRect:NSMakeRect(0, 0, 400, 250)
                                                         styleMask:(NSWindowStyleMaskTitled | NSWindowStyleMaskClosable)
                                                           backing:NSBackingStoreBuffered
                                                             defer:NO];
    self.preferencesWindow.title = @"Preferences";
    [self.preferencesWindow center];

    NSView *contentView = [[NSView alloc] initWithFrame:self.preferencesWindow.contentView.bounds];

    // Theme label
    NSTextField *themeLabel = [[NSTextField alloc] initWithFrame:NSMakeRect(20, 200, 100, 20)];
    themeLabel.stringValue = @"Terminal Theme:";
    themeLabel.bordered = NO;
    themeLabel.backgroundColor = [NSColor clearColor];
    themeLabel.editable = NO;
    [contentView addSubview:themeLabel];

    // Theme buttons
    NSButton *amberButton = [[NSButton alloc] initWithFrame:NSMakeRect(140, 195, 120, 25)];
    [amberButton setButtonType:NSButtonTypeRadio];
    amberButton.title = @"VT220 Amber";
    amberButton.state = (self.theme == ColorThemeAmber) ? NSControlStateValueOn : NSControlStateValueOff;
    amberButton.tag = ColorThemeAmber;
    amberButton.target = self;
    amberButton.action = @selector(themeChanged:);
    [contentView addSubview:amberButton];

    NSButton *blueButton = [[NSButton alloc] initWithFrame:NSMakeRect(140, 170, 120, 25)];
    [blueButton setButtonType:NSButtonTypeRadio];
    blueButton.title = @"DEC Blue";
    blueButton.state = (self.theme == ColorThemeDECBlue) ? NSControlStateValueOn : NSControlStateValueOff;
    blueButton.tag = ColorThemeDECBlue;
    blueButton.target = self;
    blueButton.action = @selector(themeChanged:);
    [contentView addSubview:blueButton];

    NSButton *greenButton = [[NSButton alloc] initWithFrame:NSMakeRect(140, 145, 120, 25)];
    [greenButton setButtonType:NSButtonTypeRadio];
    greenButton.title = @"IBM 3270";
    greenButton.state = (self.theme == ColorThemeIBM3270) ? NSControlStateValueOn : NSControlStateValueOff;
    greenButton.tag = ColorThemeIBM3270;
    greenButton.target = self;
    greenButton.action = @selector(themeChanged:);
    [contentView addSubview:greenButton];

    // Font label
    NSTextField *fontLabel = [[NSTextField alloc] initWithFrame:NSMakeRect(20, 100, 100, 20)];
    fontLabel.stringValue = @"Font:";
    fontLabel.bordered = NO;
    fontLabel.backgroundColor = [NSColor clearColor];
    fontLabel.editable = NO;
    [contentView addSubview:fontLabel];

    // Font selection button
    self.fontButton = [[NSButton alloc] initWithFrame:NSMakeRect(140, 95, 220, 25)];
    self.fontButton.title = [NSString stringWithFormat:@"%@ %.0f pt", self.textView.font.displayName, self.textView.font.pointSize];
    self.fontButton.bezelStyle = NSBezelStyleRounded;
    self.fontButton.target = self;
    self.fontButton.action = @selector(selectFont:);
    [contentView addSubview:self.fontButton];

    // Close button
    NSButton *closeButton = [[NSButton alloc] initWithFrame:NSMakeRect(300, 20, 80, 32)];
    closeButton.title = @"Close";
    closeButton.bezelStyle = NSBezelStyleRounded;
    closeButton.keyEquivalent = @"\r";
    closeButton.target = self.preferencesWindow;
    closeButton.action = @selector(close);
    [contentView addSubview:closeButton];

    self.preferencesWindow.contentView = contentView;
    [self.preferencesWindow makeKeyAndOrderFront:nil];
}

- (void)themeChanged:(NSButton *)sender {
    ColorTheme newTheme = (ColorTheme)sender.tag;

    // Save preference
    [[NSUserDefaults standardUserDefaults] setInteger:newTheme forKey:@"ColorTheme"];
    [[NSUserDefaults standardUserDefaults] synchronize];

    // Close preferences window first
    if (self.preferencesWindow) {
        [self.preferencesWindow close];
        self.preferencesWindow = nil;
    }

    // Apply theme on main thread with slight delay to ensure window is closed
    dispatch_after(dispatch_time(DISPATCH_TIME_NOW, (int64_t)(0.1 * NSEC_PER_SEC)), dispatch_get_main_queue(), ^{
        self.theme = newTheme;
        [self applyTheme];
    });
}

- (void)selectFont:(id)sender {
    // Make main window key so it receives font panel messages
    [self.window makeKeyAndOrderFront:nil];

    NSFontManager *fontManager = [NSFontManager sharedFontManager];
    [fontManager setSelectedFont:self.textView.font isMultiple:NO];
    [fontManager setTarget:self];
    [fontManager setAction:@selector(changeFont:)];

    NSFontPanel *fontPanel = [fontManager fontPanel:YES];
    [fontPanel makeKeyAndOrderFront:sender];
}

- (void)changeFont:(id)sender {
    NSFontManager *fontManager = [NSFontManager sharedFontManager];
    NSFont *newFont = [fontManager convertFont:self.textView.font];

    if (!newFont) return;

    // Save font preference
    NSData *fontData = [NSArchiver archivedDataWithRootObject:newFont];
    [[NSUserDefaults standardUserDefaults] setObject:fontData forKey:@"TerminalFont"];

    // Just update font for new text - don't touch existing text
    self.textView.font = newFont;
    [self.textView setTypingAttributes:@{
        NSForegroundColorAttributeName: [self textColor],
        NSFontAttributeName: newFont
    }];

    // Update button
    if (self.fontButton) {
        self.fontButton.title = [NSString stringWithFormat:@"%@ %.0f pt", newFont.displayName, newFont.pointSize];
    }
}

- (void)applyTheme {
    // Update all UI colors
    self.textView.backgroundColor = [self backgroundColor];
    self.textView.textColor = [self textColor];
    self.textView.insertionPointColor = [self textColor];
    [self.textView setTypingAttributes:@{
        NSForegroundColorAttributeName: [self textColor],
        NSFontAttributeName: self.textView.font
    }];

    NSView *container = self.window.contentView;
    container.layer.backgroundColor = [[self backgroundColor] CGColor];

    NSString *themeName = self.theme == ColorThemeDECBlue ? @"DEC Blue" :
                         self.theme == ColorThemeIBM3270 ? @"IBM 3270" : @"VT220 Amber";

    // Safe text append
    @try {
        [self appendText:[NSString stringWithFormat:@"\nTheme: %@\n", themeName] color:[self dimTextColor]];
        [self showPrompt];
    } @catch (NSException *e) {
        NSLog(@"Error in applyTheme: %@", e);
    }
}

- (void)showHelpCommands:(id)sender {
    NSAlert *alert = [[NSAlert alloc] init];
    alert.messageText = @"Available Commands";
    alert.informativeText = @"Novice mode (% prompt):\n"
                            @"  help - Show available commands\n"
                            @"  describe <thing> - Explain what something is\n"
                            @"  inspect <thing> - Show contents\n\n"
                            @"Schemer mode (λ prompt):\n"
                            @"  (help) - Show REPL commands\n"
                            @"  (sicp) - Display LOC/λ metrics\n"
                            @"  (version) - Show version\n"
                            @"  (novice) - Switch to novice mode\n"
                            @"  (schemer) - Switch to schemer mode\n\n"
                            @"Type ( or , to enter schemer mode automatically.";
    alert.alertStyle = NSAlertStyleInformational;
    [alert addButtonWithTitle:@"OK"];
    [alert runModal];
}

- (void)showHelpVault:(id)sender {
    NSAlert *alert = [[NSAlert alloc] init];
    alert.messageText = @"Vault and Storage";
    alert.informativeText = @"The vault stores objects in a content-addressed soup using S-expressions.\n\n"
                            @"Commands:\n"
                            @"  (vault-status) - Show vault status and statistics\n"
                            @"  (vault-path) - Display vault location\n"
                            @"  (catalog) - List vault contents\n"
                            @"  (soup-info) - Show soup structure\n\n"
                            @"The vault uses cryptographic hashes for object addressing and maintains "
                            @"audit trails for all operations.";
    alert.alertStyle = NSAlertStyleInformational;
    [alert addButtonWithTitle:@"OK"];
    [alert runModal];
}

- (void)showHelpRealm:(id)sender {
    NSAlert *alert = [[NSAlert alloc] init];
    alert.messageText = @"Realm Status and Management";
    alert.informativeText = @"A realm represents a single administrative domain with its own "
                            @"cryptographic identity and membership.\n\n"
                            @"Commands:\n"
                            @"  (realm-status) - Display current realm state\n"
                            @"  (realm-info) - Show realm configuration\n"
                            @"  (membership) - List realm members\n"
                            @"  (enrollment-status) - Check enrollment state\n\n"
                            @"Single-realm model: Enclaves with separate consensus policies "
                            @"are deferred as future work.";
    alert.alertStyle = NSAlertStyleInformational;
    [alert addButtonWithTitle:@"OK"];
    [alert runModal];
}

- (void)showHelpSPKI:(id)sender {
    NSAlert *alert = [[NSAlert alloc] init];
    alert.messageText = @"SPKI Certificates and Authorization";
    alert.informativeText = @"Simple Public Key Infrastructure for authorization and delegation.\n\n"
                            @"Commands:\n"
                            @"  (make-cert ...) - Create SPKI certificate\n"
                            @"  (verify-cert c) - Verify certificate validity\n"
                            @"  (show-cert c) - Display certificate details\n"
                            @"  (cert-chain c) - Show certificate chain\n\n"
                            @"SPKI certificates bind authorization to public keys rather than names, "
                            @"supporting delegation and capability-based security.";
    alert.alertStyle = NSAlertStyleInformational;
    [alert addButtonWithTitle:@"OK"];
    [alert runModal];
}

- (void)showHelpCrypto:(id)sender {
    NSAlert *alert = [[NSAlert alloc] init];
    alert.messageText = @"Cryptographic Operations";
    alert.informativeText = @"Ed25519 signatures with Blake2b hashing.\n\n"
                            @"Commands:\n"
                            @"  (keygen) - Generate Ed25519 key pair\n"
                            @"  (sign data) - Sign data with private key\n"
                            @"  (verify sig) - Verify signature\n"
                            @"  (hash data) - Blake2b hash computation\n"
                            @"  (keyring-list) - Show available keys\n\n"
                            @"All cryptographic operations maintain audit trails and "
                            @"use FIPS-compliant implementations where available.";
    alert.alertStyle = NSAlertStyleInformational;
    [alert addButtonWithTitle:@"OK"];
    [alert runModal];
}

- (void)showHelpModules:(id)sender {
    NSAlert *alert = [[NSAlert alloc] init];
    alert.messageText = @"Available Modules and Libraries";
    alert.informativeText = @"Core modules by category:\n\n"
                            @"Foundation: sexp, capability, fips, audit\n"
                            @"Crypto: crypto-ffi, keyring, cert, security\n"
                            @"Storage: vault, catalog, bloom\n"
                            @"Network: gossip, http, server\n"
                            @"Enrollment: enroll, auto-enroll\n"
                            @"Tools: inspector, scrutinizer, mpe, pencil, repl\n"
                            @"Content: forum, filetype, display, info, wordlist\n\n"
                            @"Use (sicp) in the REPL for current metrics and detailed per-module analysis.";
    alert.alertStyle = NSAlertStyleInformational;
    [alert addButtonWithTitle:@"OK"];
    [alert runModal];
}

- (void)showAbout:(id)sender {
    NSDate *now = [NSDate date];
    NSDateFormatter *timeFormatter = [[NSDateFormatter alloc] init];
    [timeFormatter setDateFormat:@"HH:mm:ss"];
    NSString *currentTime = [timeFormatter stringFromDate:now];

    NSCalendar *calendar = [NSCalendar currentCalendar];
    NSDateComponents *components = [calendar components:NSCalendarUnitHour fromDate:now];
    NSInteger hour = components.hour;
    NSString *currentPrahar = [self praharNameForHour:hour];

    // Get metrics safely - just count and total
    NSString *metrics = @"~25 modules";
    @try {
        char *modResult = scheme_eval("(length *cyberspace-modules*)");
        if (modResult) {
            NSString *count = [[NSString stringWithUTF8String:modResult] stringByTrimmingCharactersInSet:[NSCharacterSet whitespaceAndNewlineCharacterSet]];
            metrics = [NSString stringWithFormat:@"%@ modules", count];
            scheme_free_result(modResult);
        }
    } @catch (NSException *e) {
        NSLog(@"Error getting module count: %@", e);
    }

    NSAlert *alert = [[NSAlert alloc] init];
    alert.messageText = @"Library of Cyberspace";
    alert.informativeText = [NSString stringWithFormat:
                            @"Version 0.4.0\n\n"
                            @"Distributed preservation with cryptographic audit trails and SPKI authorization.\n\n"
                            @"%@ — use (sicp) for detailed metrics\n\n"
                            @"The Praha Lambda (λ) breathes with the weave—its color morphs through the prahar (watches) of the day:\n\n"
                            @"brahma muhūrta (ब्रह्म मुहूर्त) · violet · prātaḥkāla (प्रातःकाल) · gold\n"
                            @"saṅgava (सङ्गव) · teal · madhyāhna (मध्याह्न) · phosphor\n"
                            @"aparāhṇa (अपराह्ण) · neon · sāyāhna (सायाह्न) · orange\n"
                            @"pradoṣa (प्रदोष) · coral · niśītha (निशीथ) · cyan\n\n"
                            @"Devanāgarī (देवनागरी)—city of the gods—marks the watches of a lambda breathing in Cyberspace.\n\n"
                            @"Local time: %@ · %@", metrics, currentTime, currentPrahar];
    alert.alertStyle = NSAlertStyleInformational;

    NSImage *icon = [NSApp applicationIconImage];
    if (icon) {
        alert.icon = icon;
    }

    [alert addButtonWithTitle:@"OK"];
    [alert runModal];
}

- (void)applicationWillTerminate:(NSNotification *)notification {
    [self saveHistory];
    scheme_cleanup();
}

@end

// C bridge function to show About from Scheme
void scheme_show_about(void) {
    dispatch_async(dispatch_get_main_queue(), ^{
        if (g_delegate) {
            [g_delegate showAbout:nil];
        }
    });
}

int main(int argc, char *argv[]) {
    @autoreleasepool {
        NSApplication *app = [NSApplication sharedApplication];
        CyberspaceNativeREPL *delegate = [[CyberspaceNativeREPL alloc] init];
        app.delegate = delegate;
        [app run];
    }
    return 0;
}
