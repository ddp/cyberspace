/*
 * Cyberspace.app - Native macOS Shell
 * Library of Cyberspace
 *
 * Minimal Cocoa app embedding WKWebView connected to Scheme backend.
 * Architecture: Swappable WebView (WKWebView now, CEF option later)
 *
 * Security integrations:
 * - Keychain Access: Store/retrieve cryptographic keys
 * - Kerberos: Enterprise SSO authentication
 */

#import <Cocoa/Cocoa.h>
#import <WebKit/WebKit.h>
#import <Security/Security.h>
#import <GSS/GSS.h>

// ============================================================================
// CyberWebView Protocol - Abstraction for swappable WebView implementations
// ============================================================================

@protocol CyberWebView <NSObject>
- (void)loadURL:(NSURL *)url;
- (void)evaluateJavaScript:(NSString *)js
         completionHandler:(void (^)(id result, NSError *error))handler;
- (void)setMessageHandler:(void (^)(NSDictionary *message))handler;
- (void)postMessage:(NSDictionary *)message;
- (NSView *)view;
@end

// ============================================================================
// WKWebViewAdapter - WebKit implementation of CyberWebView
// ============================================================================

@interface WKWebViewAdapter : NSObject <CyberWebView, WKScriptMessageHandler, WKNavigationDelegate>
@property (nonatomic, strong) WKWebView *webView;
@property (nonatomic, copy) void (^messageHandler)(NSDictionary *);
@end

@implementation WKWebViewAdapter

- (instancetype)init {
    self = [super init];
    if (self) {
        WKWebViewConfiguration *config = [[WKWebViewConfiguration alloc] init];
        WKUserContentController *userContent = [[WKUserContentController alloc] init];

        // Register message handler for JS -> native communication
        [userContent addScriptMessageHandler:self name:@"cyberspace"];
        config.userContentController = userContent;

        // Enable developer extras (right-click inspect)
        [config.preferences setValue:@YES forKey:@"developerExtrasEnabled"];

        _webView = [[WKWebView alloc] initWithFrame:NSZeroRect configuration:config];
        _webView.navigationDelegate = self;

        // Allow file:// URLs to load local resources
        [_webView.configuration.preferences setValue:@YES
                                              forKey:@"allowFileAccessFromFileURLs"];
    }
    return self;
}

- (void)loadURL:(NSURL *)url {
    NSURLRequest *request = [NSURLRequest requestWithURL:url];
    [self.webView loadRequest:request];
}

- (void)evaluateJavaScript:(NSString *)js
         completionHandler:(void (^)(id, NSError *))handler {
    [self.webView evaluateJavaScript:js completionHandler:handler];
}

- (void)setMessageHandler:(void (^)(NSDictionary *))handler {
    _messageHandler = handler;
}

- (void)postMessage:(NSDictionary *)message {
    NSError *error;
    NSData *jsonData = [NSJSONSerialization dataWithJSONObject:message
                                                       options:0
                                                         error:&error];
    if (jsonData) {
        NSString *jsonString = [[NSString alloc] initWithData:jsonData
                                                     encoding:NSUTF8StringEncoding];
        NSString *js = [NSString stringWithFormat:
                        @"window.dispatchEvent(new CustomEvent('cyberspace', {detail: %@}));",
                        jsonString];
        [self evaluateJavaScript:js completionHandler:nil];
    }
}

- (NSView *)view {
    return self.webView;
}

// WKScriptMessageHandler - receive messages from JavaScript
- (void)userContentController:(WKUserContentController *)userContentController
      didReceiveScriptMessage:(WKScriptMessage *)message {
    if ([message.name isEqualToString:@"cyberspace"] && self.messageHandler) {
        if ([message.body isKindOfClass:[NSDictionary class]]) {
            self.messageHandler(message.body);
        }
    }
}

// WKNavigationDelegate
- (void)webView:(WKWebView *)webView
didFailNavigation:(WKNavigation *)navigation
      withError:(NSError *)error {
    NSLog(@"[Cyberspace] Navigation failed: %@", error.localizedDescription);
}

- (void)webView:(WKWebView *)webView
didFinishNavigation:(WKNavigation *)navigation {
    NSLog(@"[Cyberspace] Page loaded");
    // Focus the webview and terminal
    [webView becomeFirstResponder];
    [webView evaluateJavaScript:@"if(term) term.focus();" completionHandler:nil];
}

@end

// ============================================================================
// PreferencesManager - User preferences with NSUserDefaults
// ============================================================================

@interface PreferencesManager : NSObject
+ (void)saveWindowFrame:(NSRect)frame;
+ (NSRect)windowFrame;
+ (void)setFontName:(NSString *)name size:(CGFloat)size;
+ (NSString *)fontName;
+ (CGFloat)fontSize;
+ (void)setTheme:(NSString *)theme;
+ (NSString *)theme;
+ (NSDictionary *)allPreferences;
@end

@implementation PreferencesManager

+ (void)initialize {
    // Register defaults
    [[NSUserDefaults standardUserDefaults] registerDefaults:@{
        @"windowX": @100,
        @"windowY": @100,
        @"windowWidth": @1200,
        @"windowHeight": @800,
        @"fontName": @"SF Mono",
        @"fontSize": @13,
        @"theme": @"dark"
    }];
}

+ (void)saveWindowFrame:(NSRect)frame {
    NSUserDefaults *defaults = [NSUserDefaults standardUserDefaults];
    [defaults setDouble:frame.origin.x forKey:@"windowX"];
    [defaults setDouble:frame.origin.y forKey:@"windowY"];
    [defaults setDouble:frame.size.width forKey:@"windowWidth"];
    [defaults setDouble:frame.size.height forKey:@"windowHeight"];
    [defaults synchronize];
}

+ (NSRect)windowFrame {
    NSUserDefaults *defaults = [NSUserDefaults standardUserDefaults];
    return NSMakeRect(
        [defaults doubleForKey:@"windowX"],
        [defaults doubleForKey:@"windowY"],
        [defaults doubleForKey:@"windowWidth"],
        [defaults doubleForKey:@"windowHeight"]
    );
}

+ (void)setFontName:(NSString *)name size:(CGFloat)size {
    NSUserDefaults *defaults = [NSUserDefaults standardUserDefaults];
    [defaults setObject:name forKey:@"fontName"];
    [defaults setDouble:size forKey:@"fontSize"];
    [defaults synchronize];
}

+ (NSString *)fontName {
    return [[NSUserDefaults standardUserDefaults] stringForKey:@"fontName"];
}

+ (CGFloat)fontSize {
    return [[NSUserDefaults standardUserDefaults] doubleForKey:@"fontSize"];
}

+ (void)setTheme:(NSString *)theme {
    [[NSUserDefaults standardUserDefaults] setObject:theme forKey:@"theme"];
    [[NSUserDefaults standardUserDefaults] synchronize];
}

+ (NSString *)theme {
    return [[NSUserDefaults standardUserDefaults] stringForKey:@"theme"];
}

+ (NSDictionary *)allPreferences {
    return @{
        @"fontName": [self fontName],
        @"fontSize": @([self fontSize]),
        @"theme": [self theme]
    };
}

@end

// ============================================================================
// KeychainManager - Secure key storage via macOS Keychain
// ============================================================================

@interface KeychainManager : NSObject
+ (BOOL)storeKey:(NSData *)keyData forIdentifier:(NSString *)identifier;
+ (NSData *)retrieveKeyForIdentifier:(NSString *)identifier;
+ (BOOL)deleteKeyForIdentifier:(NSString *)identifier;
+ (NSArray<NSString *> *)listKeyIdentifiers;
@end

@implementation KeychainManager

+ (BOOL)storeKey:(NSData *)keyData forIdentifier:(NSString *)identifier {
    // Delete any existing key first
    [self deleteKeyForIdentifier:identifier];

    NSString *service = @"com.yoyodyne.cyberspace.keys";
    NSDictionary *query = @{
        (__bridge id)kSecClass: (__bridge id)kSecClassGenericPassword,
        (__bridge id)kSecAttrService: service,
        (__bridge id)kSecAttrAccount: identifier,
        (__bridge id)kSecValueData: keyData,
        (__bridge id)kSecAttrAccessible: (__bridge id)kSecAttrAccessibleWhenUnlockedThisDeviceOnly
    };

    OSStatus status = SecItemAdd((__bridge CFDictionaryRef)query, NULL);
    if (status != errSecSuccess) {
        NSLog(@"[Keychain] Failed to store key '%@': %d", identifier, (int)status);
        return NO;
    }
    NSLog(@"[Keychain] Stored key '%@'", identifier);
    return YES;
}

+ (NSData *)retrieveKeyForIdentifier:(NSString *)identifier {
    NSString *service = @"com.yoyodyne.cyberspace.keys";
    NSDictionary *query = @{
        (__bridge id)kSecClass: (__bridge id)kSecClassGenericPassword,
        (__bridge id)kSecAttrService: service,
        (__bridge id)kSecAttrAccount: identifier,
        (__bridge id)kSecReturnData: @YES,
        (__bridge id)kSecMatchLimit: (__bridge id)kSecMatchLimitOne
    };

    CFTypeRef result = NULL;
    OSStatus status = SecItemCopyMatching((__bridge CFDictionaryRef)query, &result);

    if (status == errSecSuccess && result != NULL) {
        NSData *data = (__bridge_transfer NSData *)result;
        NSLog(@"[Keychain] Retrieved key '%@'", identifier);
        return data;
    }

    if (status != errSecItemNotFound) {
        NSLog(@"[Keychain] Failed to retrieve key '%@': %d", identifier, (int)status);
    }
    return nil;
}

+ (BOOL)deleteKeyForIdentifier:(NSString *)identifier {
    NSString *service = @"com.yoyodyne.cyberspace.keys";
    NSDictionary *query = @{
        (__bridge id)kSecClass: (__bridge id)kSecClassGenericPassword,
        (__bridge id)kSecAttrService: service,
        (__bridge id)kSecAttrAccount: identifier
    };

    OSStatus status = SecItemDelete((__bridge CFDictionaryRef)query);
    return (status == errSecSuccess || status == errSecItemNotFound);
}

+ (NSArray<NSString *> *)listKeyIdentifiers {
    NSString *service = @"com.yoyodyne.cyberspace.keys";
    NSDictionary *query = @{
        (__bridge id)kSecClass: (__bridge id)kSecClassGenericPassword,
        (__bridge id)kSecAttrService: service,
        (__bridge id)kSecReturnAttributes: @YES,
        (__bridge id)kSecMatchLimit: (__bridge id)kSecMatchLimitAll
    };

    CFTypeRef result = NULL;
    OSStatus status = SecItemCopyMatching((__bridge CFDictionaryRef)query, &result);

    if (status == errSecSuccess && result != NULL) {
        NSArray *items = (__bridge_transfer NSArray *)result;
        NSMutableArray *identifiers = [NSMutableArray array];
        for (NSDictionary *item in items) {
            NSString *account = item[(__bridge id)kSecAttrAccount];
            if (account) {
                [identifiers addObject:account];
            }
        }
        return identifiers;
    }

    return @[];
}

@end

// ============================================================================
// KerberosManager - Enterprise SSO via GSS-API
// ============================================================================

@interface KerberosManager : NSObject
+ (NSString *)currentPrincipal;
+ (BOOL)hasValidCredential;
+ (NSDictionary *)credentialInfo;
@end

@implementation KerberosManager

+ (NSString *)currentPrincipal {
    gss_cred_id_t cred = GSS_C_NO_CREDENTIAL;
    gss_name_t name = GSS_C_NO_NAME;
    OM_uint32 minor, major;

    // Acquire default credentials
    major = gss_acquire_cred(&minor, GSS_C_NO_NAME, GSS_C_INDEFINITE,
                             GSS_C_NO_OID_SET, GSS_C_INITIATE, &cred, NULL, NULL);

    if (major != GSS_S_COMPLETE) {
        return nil;
    }

    // Get the principal name
    major = gss_inquire_cred(&minor, cred, &name, NULL, NULL, NULL);
    gss_release_cred(&minor, &cred);

    if (major != GSS_S_COMPLETE || name == GSS_C_NO_NAME) {
        return nil;
    }

    // Convert to string
    gss_buffer_desc buffer = GSS_C_EMPTY_BUFFER;
    major = gss_display_name(&minor, name, &buffer, NULL);
    gss_release_name(&minor, &name);

    if (major != GSS_S_COMPLETE) {
        return nil;
    }

    NSString *principal = [[NSString alloc] initWithBytes:buffer.value
                                                   length:buffer.length
                                                 encoding:NSUTF8StringEncoding];
    gss_release_buffer(&minor, &buffer);

    NSLog(@"[Kerberos] Current principal: %@", principal);
    return principal;
}

+ (BOOL)hasValidCredential {
    return [self currentPrincipal] != nil;
}

+ (NSDictionary *)credentialInfo {
    NSString *principal = [self currentPrincipal];
    if (!principal) {
        return @{@"authenticated": @NO};
    }

    return @{
        @"authenticated": @YES,
        @"principal": principal,
        @"mechanism": @"Kerberos"
    };
}

@end

// ============================================================================
// AppDelegate
// ============================================================================

@interface AppDelegate : NSObject <NSApplicationDelegate, NSWindowDelegate>
@property (nonatomic, strong) NSWindow *window;
@property (nonatomic, strong) id<CyberWebView> webView;
@property (nonatomic, strong) NSTask *schemeBackend;
@property (nonatomic, assign) int backendPort;
@end

@implementation AppDelegate

- (void)applicationDidFinishLaunching:(NSNotification *)notification {
    // Find an available port
    self.backendPort = 7780;

    // Restore window frame from preferences
    NSRect frame = [PreferencesManager windowFrame];
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
    self.window.minSize = NSMakeSize(800, 600);
    self.window.frameAutosaveName = @"CyberspaceMainWindow";

    // Create WebView adapter (swappable)
    self.webView = [[WKWebViewAdapter alloc] init];

    // Set up message handler
    __weak AppDelegate *weakSelf = self;
    [self.webView setMessageHandler:^(NSDictionary *message) {
        [weakSelf handleWebMessage:message];
    }];

    // Add WebView to window
    NSView *webViewNS = [self.webView view];
    webViewNS.frame = self.window.contentView.bounds;
    webViewNS.autoresizingMask = NSViewWidthSizable | NSViewHeightSizable;
    [self.window.contentView addSubview:webViewNS];

    // Start the Scheme backend server
    [self startSchemeBackend];

    // Give server a moment to start, then load UI
    dispatch_after(dispatch_time(DISPATCH_TIME_NOW, (int64_t)(0.5 * NSEC_PER_SEC)),
                   dispatch_get_main_queue(), ^{
        NSURL *url = [NSURL URLWithString:
                      [NSString stringWithFormat:@"http://127.0.0.1:%d/", self.backendPort]];
        [self.webView loadURL:url];
    });

    // Show window
    [self.window makeKeyAndOrderFront:nil];

    // Set up menu
    [self setupMenu];
}

- (void)startSchemeBackend {
    NSBundle *bundle = [NSBundle mainBundle];
    NSString *resourcePath = bundle.resourcePath;

    // Look for compiled server first, then script
    NSString *serverBinary = [resourcePath stringByAppendingPathComponent:@"cyberspace-server"];
    NSString *serverScript = [resourcePath stringByAppendingPathComponent:@"cyberspace-server.scm"];
    NSString *schemeDir = @"/Users/ddp/cyberspace/spki/scheme";

    NSString *executable = nil;
    NSArray *arguments = nil;

    if ([[NSFileManager defaultManager] fileExistsAtPath:serverBinary]) {
        // Use compiled binary
        executable = serverBinary;
        arguments = @[[NSString stringWithFormat:@"%d", self.backendPort]];
    } else if ([[NSFileManager defaultManager] fileExistsAtPath:serverScript]) {
        // Use bundled script with csi
        executable = @"/opt/homebrew/bin/csi";
        arguments = @[@"-s", serverScript, [NSString stringWithFormat:@"%d", self.backendPort]];
    } else {
        // Development mode
        NSString *devScript = [schemeDir stringByAppendingPathComponent:@"cyberspace-server.scm"];
        if ([[NSFileManager defaultManager] fileExistsAtPath:devScript]) {
            executable = @"/opt/homebrew/bin/csi";
            arguments = @[@"-s", devScript, [NSString stringWithFormat:@"%d", self.backendPort]];
        }
    }

    if (!executable) {
        NSLog(@"[Cyberspace] No backend found - UI only mode");
        return;
    }

    NSLog(@"[Cyberspace] Starting backend: %@ %@", executable, arguments);

    self.schemeBackend = [[NSTask alloc] init];
    self.schemeBackend.launchPath = executable;
    self.schemeBackend.arguments = arguments;
    self.schemeBackend.currentDirectoryPath = schemeDir;

    // Capture output for logging
    NSPipe *outputPipe = [NSPipe pipe];
    self.schemeBackend.standardOutput = outputPipe;
    self.schemeBackend.standardError = outputPipe;

    // Read output asynchronously
    outputPipe.fileHandleForReading.readabilityHandler = ^(NSFileHandle *handle) {
        NSData *data = handle.availableData;
        if (data.length > 0) {
            NSString *output = [[NSString alloc] initWithData:data encoding:NSUTF8StringEncoding];
            NSLog(@"[Backend] %@", output);
        }
    };

    @try {
        [self.schemeBackend launch];
        NSLog(@"[Cyberspace] Backend started (PID %d)", self.schemeBackend.processIdentifier);
    } @catch (NSException *e) {
        NSLog(@"[Cyberspace] Failed to start backend: %@", e.reason);
    }
}

- (void)handleWebMessage:(NSDictionary *)message {
    NSString *type = message[@"type"];
    NSString *requestId = message[@"id"];
    NSLog(@"[Cyberspace] Received message: %@ - %@", type, message);

    if ([type isEqualToString:@"eval"]) {
        NSString *expr = message[@"expression"];
        NSLog(@"[Cyberspace] Eval request: %@", expr);
        // TODO: Send to Scheme backend via WebSocket

    } else if ([type isEqualToString:@"keychain.store"]) {
        NSString *identifier = message[@"identifier"];
        NSString *keyBase64 = message[@"key"];
        NSData *keyData = [[NSData alloc] initWithBase64EncodedString:keyBase64 options:0];
        BOOL success = [KeychainManager storeKey:keyData forIdentifier:identifier];
        [self.webView postMessage:@{
            @"id": requestId ?: @"",
            @"type": @"keychain.result",
            @"success": @(success)
        }];

    } else if ([type isEqualToString:@"keychain.retrieve"]) {
        NSString *identifier = message[@"identifier"];
        NSData *keyData = [KeychainManager retrieveKeyForIdentifier:identifier];
        NSString *keyBase64 = keyData ? [keyData base64EncodedStringWithOptions:0] : @"";
        [self.webView postMessage:@{
            @"id": requestId ?: @"",
            @"type": @"keychain.result",
            @"success": @(keyData != nil),
            @"key": keyBase64
        }];

    } else if ([type isEqualToString:@"keychain.delete"]) {
        NSString *identifier = message[@"identifier"];
        BOOL success = [KeychainManager deleteKeyForIdentifier:identifier];
        [self.webView postMessage:@{
            @"id": requestId ?: @"",
            @"type": @"keychain.result",
            @"success": @(success)
        }];

    } else if ([type isEqualToString:@"keychain.list"]) {
        NSArray *identifiers = [KeychainManager listKeyIdentifiers];
        [self.webView postMessage:@{
            @"id": requestId ?: @"",
            @"type": @"keychain.result",
            @"success": @YES,
            @"identifiers": identifiers
        }];

    } else if ([type isEqualToString:@"kerberos.info"]) {
        NSDictionary *info = [KerberosManager credentialInfo];
        [self.webView postMessage:@{
            @"id": requestId ?: @"",
            @"type": @"kerberos.result",
            @"info": info
        }];
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

    // Edit menu (for copy/paste)
    NSMenuItem *editMenuItem = [[NSMenuItem alloc] init];
    NSMenu *editMenu = [[NSMenu alloc] initWithTitle:@"Edit"];

    [editMenu addItemWithTitle:@"Cut" action:@selector(cut:) keyEquivalent:@"x"];
    [editMenu addItemWithTitle:@"Copy" action:@selector(copy:) keyEquivalent:@"c"];
    [editMenu addItemWithTitle:@"Paste" action:@selector(paste:) keyEquivalent:@"v"];
    [editMenu addItemWithTitle:@"Select All" action:@selector(selectAll:) keyEquivalent:@"a"];

    editMenuItem.submenu = editMenu;
    [menuBar addItem:editMenuItem];

    // View menu
    NSMenuItem *viewMenuItem = [[NSMenuItem alloc] init];
    NSMenu *viewMenu = [[NSMenu alloc] initWithTitle:@"View"];

    [viewMenu addItemWithTitle:@"Reload"
                        action:@selector(reloadPage:)
                 keyEquivalent:@"r"];
    [viewMenu addItemWithTitle:@"Developer Tools"
                        action:@selector(toggleDevTools:)
                 keyEquivalent:@"i"];
    [viewMenu addItem:[NSMenuItem separatorItem]];

    // Theme submenu
    NSMenuItem *themeMenuItem = [[NSMenuItem alloc] initWithTitle:@"Theme" action:nil keyEquivalent:@""];
    NSMenu *themeMenu = [[NSMenu alloc] initWithTitle:@"Theme"];
    [themeMenu addItemWithTitle:@"Dark" action:@selector(setThemeDark:) keyEquivalent:@""];
    [themeMenu addItemWithTitle:@"Light" action:@selector(setThemeLight:) keyEquivalent:@""];
    [themeMenu addItemWithTitle:@"Solarized" action:@selector(setThemeSolarized:) keyEquivalent:@""];
    themeMenuItem.submenu = themeMenu;
    [viewMenu addItem:themeMenuItem];

    viewMenuItem.submenu = viewMenu;
    [menuBar addItem:viewMenuItem];

    // Format menu (Font)
    NSMenuItem *formatMenuItem = [[NSMenuItem alloc] init];
    NSMenu *formatMenu = [[NSMenu alloc] initWithTitle:@"Format"];

    NSMenuItem *fontMenuItem = [[NSMenuItem alloc] initWithTitle:@"Font" action:nil keyEquivalent:@""];
    NSMenu *fontMenu = [[NSMenu alloc] initWithTitle:@"Font"];
    [fontMenu addItemWithTitle:@"SF Mono" action:@selector(setFontSFMono:) keyEquivalent:@""];
    [fontMenu addItemWithTitle:@"Menlo" action:@selector(setFontMenlo:) keyEquivalent:@""];
    [fontMenu addItemWithTitle:@"Monaco" action:@selector(setFontMonaco:) keyEquivalent:@""];
    [fontMenu addItemWithTitle:@"IBM Plex Mono" action:@selector(setFontIBMPlex:) keyEquivalent:@""];
    [fontMenu addItemWithTitle:@"Bitstream Vera Sans Mono" action:@selector(setFontBitstreamVera:) keyEquivalent:@""];
    [fontMenu addItemWithTitle:@"Courier New" action:@selector(setFontCourier:) keyEquivalent:@""];
    [fontMenu addItem:[NSMenuItem separatorItem]];
    [fontMenu addItemWithTitle:@"Show Fonts..." action:@selector(showFontPanel:) keyEquivalent:@"t"];
    fontMenuItem.submenu = fontMenu;
    [formatMenu addItem:fontMenuItem];

    // Font size
    [formatMenu addItemWithTitle:@"Bigger" action:@selector(increaseFontSize:) keyEquivalent:@"+"];
    [formatMenu addItemWithTitle:@"Smaller" action:@selector(decreaseFontSize:) keyEquivalent:@"-"];

    formatMenuItem.submenu = formatMenu;
    [menuBar addItem:formatMenuItem];

    // Window menu
    NSMenuItem *windowMenuItem = [[NSMenuItem alloc] init];
    NSMenu *windowMenu = [[NSMenu alloc] initWithTitle:@"Window"];

    [windowMenu addItemWithTitle:@"Minimize"
                          action:@selector(performMiniaturize:)
                   keyEquivalent:@"m"];
    [windowMenu addItemWithTitle:@"Zoom"
                          action:@selector(performZoom:)
                   keyEquivalent:@""];

    windowMenuItem.submenu = windowMenu;
    [menuBar addItem:windowMenuItem];

    [NSApp setMainMenu:menuBar];
}

- (void)showAbout:(id)sender {
    NSAlert *alert = [[NSAlert alloc] init];
    alert.messageText = @"Cyberspace";
    alert.informativeText = @"Library of Cyberspace\n\n"
                           @"A distributed preservation system with\n"
                           @"cryptographic audit trails and SPKI authorization.\n\n"
                           @"Copyright 2026 Yoyodyne";
    alert.alertStyle = NSAlertStyleInformational;
    [alert runModal];
}

- (void)reloadPage:(id)sender {
    NSURL *url = [NSURL URLWithString:
                  [NSString stringWithFormat:@"http://127.0.0.1:%d/", self.backendPort]];
    [self.webView loadURL:url];
}

- (void)toggleDevTools:(id)sender {
    // WebKit inspector can be opened via right-click menu
    // For programmatic access, would need private API
    NSLog(@"[Cyberspace] Use right-click > Inspect Element for DevTools");
}

// Theme actions
- (void)setThemeDark:(id)sender {
    [self applyTheme:@"dark"];
}

- (void)setThemeLight:(id)sender {
    [self applyTheme:@"light"];
}

- (void)setThemeSolarized:(id)sender {
    [self applyTheme:@"solarized"];
}

- (void)applyTheme:(NSString *)theme {
    [PreferencesManager setTheme:theme];
    [self.webView postMessage:@{@"type": @"preferences.theme", @"theme": theme}];
}

// Font actions
- (void)setFontSFMono:(id)sender {
    [self applyFont:@"SF Mono"];
}

- (void)setFontMenlo:(id)sender {
    [self applyFont:@"Menlo"];
}

- (void)setFontMonaco:(id)sender {
    [self applyFont:@"Monaco"];
}

- (void)setFontCourier:(id)sender {
    [self applyFont:@"Courier New"];
}

- (void)setFontIBMPlex:(id)sender {
    [self applyFont:@"IBM Plex Mono"];
}

- (void)setFontBitstreamVera:(id)sender {
    [self applyFont:@"Bitstream Vera Sans Mono"];
}

- (void)applyFont:(NSString *)fontName {
    CGFloat size = [PreferencesManager fontSize];
    [PreferencesManager setFontName:fontName size:size];
    [self.webView postMessage:@{
        @"type": @"preferences.font",
        @"fontName": fontName,
        @"fontSize": @(size)
    }];
}

- (void)increaseFontSize:(id)sender {
    CGFloat size = [PreferencesManager fontSize] + 1;
    if (size > 24) size = 24;
    NSString *fontName = [PreferencesManager fontName];
    [PreferencesManager setFontName:fontName size:size];
    [self.webView postMessage:@{
        @"type": @"preferences.font",
        @"fontName": fontName,
        @"fontSize": @(size)
    }];
}

- (void)decreaseFontSize:(id)sender {
    CGFloat size = [PreferencesManager fontSize] - 1;
    if (size < 9) size = 9;
    NSString *fontName = [PreferencesManager fontName];
    [PreferencesManager setFontName:fontName size:size];
    [self.webView postMessage:@{
        @"type": @"preferences.font",
        @"fontName": fontName,
        @"fontSize": @(size)
    }];
}

- (void)showFontPanel:(id)sender {
    NSFontManager *fontManager = [NSFontManager sharedFontManager];
    NSFont *currentFont = [NSFont fontWithName:[PreferencesManager fontName]
                                          size:[PreferencesManager fontSize]];
    [fontManager setSelectedFont:currentFont isMultiple:NO];
    [fontManager orderFrontFontPanel:self];
}

- (BOOL)applicationShouldTerminateAfterLastWindowClosed:(NSApplication *)sender {
    return YES;
}

- (void)applicationWillTerminate:(NSNotification *)notification {
    // Clean up backend process
    if (self.schemeBackend && self.schemeBackend.isRunning) {
        [self.schemeBackend terminate];
    }
}

- (void)windowWillClose:(NSNotification *)notification {
    [NSApp terminate:nil];
}

- (void)windowDidResize:(NSNotification *)notification {
    [PreferencesManager saveWindowFrame:self.window.frame];
}

- (void)windowDidMove:(NSNotification *)notification {
    [PreferencesManager saveWindowFrame:self.window.frame];
}

@end

// ============================================================================
// Main
// ============================================================================

int main(int argc, const char *argv[]) {
    @autoreleasepool {
        NSApplication *app = [NSApplication sharedApplication];
        AppDelegate *delegate = [[AppDelegate alloc] init];
        app.delegate = delegate;
        [app run];
    }
    return 0;
}
