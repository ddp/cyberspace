/* Cyberspace - GTK4/WebKitGTK Application
 * Library of Cyberspace - Native GNOME/Fedora GUI
 *
 * A polished native Linux application using:
 *   - GTK4 for modern windowing
 *   - WebKitGTK for web rendering
 *   - libadwaita for GNOME design system
 *   - Chez Scheme backend
 *
 * Copyright (c) 2026 Yoyodyne. See LICENSE.
 */

#include <gtk/gtk.h>
#include <webkit2/webkit2.h>
#include <adwaita.h>
#include <stdlib.h>
#include <unistd.h>
#include <signal.h>
#include <sys/wait.h>

/* Configuration */
#define APP_ID "com.yoyodyne.cyberspace"
#define APP_NAME "Cyberspace"
#define SERVER_PORT 7780
#define SERVER_URL "http://127.0.0.1:7780"
#define WINDOW_WIDTH 1200
#define WINDOW_HEIGHT 800

/* Global state */
static pid_t server_pid = 0;
static GtkWidget *main_window = NULL;
static WebKitWebView *webview = NULL;

/* Start the Chez Scheme server */
static gboolean start_server(void) {
    char port_str[16];
    char *scheme_path;

    snprintf(port_str, sizeof(port_str), "%d", SERVER_PORT);

    /* Try to find the server script */
    const char *search_paths[] = {
        "/usr/local/share/cyberspace/cyberspace-server.sps",
        "/usr/share/cyberspace/cyberspace-server.sps",
        "./cyberspace-server.sps",
        "../chez/application/cyberspace-server.sps",
        NULL
    };

    scheme_path = NULL;
    for (int i = 0; search_paths[i]; i++) {
        if (access(search_paths[i], R_OK) == 0) {
            scheme_path = g_strdup(search_paths[i]);
            break;
        }
    }

    if (!scheme_path) {
        g_warning("Could not find cyberspace-server.sps");
        return FALSE;
    }

    server_pid = fork();

    if (server_pid == 0) {
        /* Child process - run the server */
        char *libdirs = g_path_get_dirname(scheme_path);

        execlp("chez", "chez",
               "--libdirs", libdirs,
               "--script", scheme_path,
               port_str,
               NULL);

        /* If exec fails */
        g_critical("Failed to start Chez Scheme server");
        exit(1);
    } else if (server_pid < 0) {
        g_critical("Failed to fork server process");
        g_free(scheme_path);
        return FALSE;
    }

    g_free(scheme_path);

    /* Give server time to start */
    g_usleep(500000); /* 500ms */

    return TRUE;
}

/* Stop the server */
static void stop_server(void) {
    if (server_pid > 0) {
        kill(server_pid, SIGTERM);
        waitpid(server_pid, NULL, 0);
        server_pid = 0;
    }
}

/* WebView load failed handler */
static gboolean on_load_failed(WebKitWebView *web_view,
                               WebKitLoadEvent load_event,
                               gchar *failing_uri,
                               GError *error,
                               gpointer user_data) {
    if (error->code == WEBKIT_NETWORK_ERROR_CANCELLED) {
        return FALSE;
    }

    g_warning("Failed to load %s: %s", failing_uri, error->message);

    /* Show error page */
    const char *error_html =
        "<!DOCTYPE html>"
        "<html><head><meta charset='utf-8'>"
        "<style>"
        "  body { font-family: system-ui; padding: 2em; max-width: 600px; margin: 0 auto; }"
        "  h1 { color: #e01b24; }"
        "  code { background: #f6f5f4; padding: 0.2em 0.4em; border-radius: 4px; }"
        "</style></head><body>"
        "<h1>⚠ Server Not Running</h1>"
        "<p>The Cyberspace server failed to start.</p>"
        "<p><strong>Error:</strong> <code>%s</code></p>"
        "<p><strong>Troubleshooting:</strong></p><ul>"
        "<li>Check that Chez Scheme is installed: <code>chez --version</code></li>"
        "<li>Verify the server script is accessible</li>"
        "<li>Check if port %d is already in use</li>"
        "</ul></body></html>";

    char *html = g_strdup_printf(error_html, error->message, SERVER_PORT);
    webkit_web_view_load_html(web_view, html, NULL);
    g_free(html);

    return TRUE;
}

/* WebView load changed handler */
static void on_load_changed(WebKitWebView *web_view,
                            WebKitLoadEvent load_event,
                            gpointer user_data) {
    switch (load_event) {
    case WEBKIT_LOAD_STARTED:
        g_debug("Loading started");
        break;
    case WEBKIT_LOAD_COMMITTED:
        g_debug("Loading committed");
        break;
    case WEBKIT_LOAD_FINISHED:
        g_debug("Loading finished");
        break;
    default:
        break;
    }
}

/* Create and configure WebView */
static WebKitWebView *create_webview(void) {
    WebKitSettings *settings = webkit_settings_new();

    /* Enable modern web features */
    webkit_settings_set_enable_developer_extras(settings, TRUE);
    webkit_settings_set_enable_webgl(settings, TRUE);
    webkit_settings_set_enable_media_stream(settings, TRUE);
    webkit_settings_set_enable_webaudio(settings, TRUE);
    webkit_settings_set_javascript_can_access_clipboard(settings, TRUE);
    webkit_settings_set_enable_back_forward_navigation_gestures(settings, TRUE);

    /* Use system fonts */
    webkit_settings_set_default_font_family(settings, "system-ui");
    webkit_settings_set_serif_font_family(settings, "serif");
    webkit_settings_set_sans_serif_font_family(settings, "sans-serif");
    webkit_settings_set_monospace_font_family(settings, "monospace");

    WebKitWebView *view = WEBKIT_WEB_VIEW(webkit_web_view_new_with_settings(settings));

    /* Connect signals */
    g_signal_connect(view, "load-failed", G_CALLBACK(on_load_failed), NULL);
    g_signal_connect(view, "load-changed", G_CALLBACK(on_load_changed), NULL);

    return view;
}

/* Application activate handler */
static void on_activate(AdwApplication *app, gpointer user_data) {
    /* Create window */
    main_window = GTK_WIDGET(adw_application_window_new(GTK_APPLICATION(app)));
    gtk_window_set_title(GTK_WINDOW(main_window), APP_NAME);
    gtk_window_set_default_size(GTK_WINDOW(main_window), WINDOW_WIDTH, WINDOW_HEIGHT);

    /* Set window icon (if available) */
    gtk_window_set_icon_name(GTK_WINDOW(main_window), APP_ID);

    /* Create header bar */
    AdwHeaderBar *header = ADW_HEADER_BAR(adw_header_bar_new());

    /* Create main box */
    GtkWidget *box = gtk_box_new(GTK_ORIENTATION_VERTICAL, 0);
    gtk_box_append(GTK_BOX(box), GTK_WIDGET(header));

    /* Create and configure WebView */
    webview = create_webview();
    gtk_widget_set_vexpand(GTK_WIDGET(webview), TRUE);
    gtk_box_append(GTK_BOX(box), GTK_WIDGET(webview));

    /* Set window content */
    adw_application_window_set_content(ADW_APPLICATION_WINDOW(main_window), box);

    /* Start the server */
    if (start_server()) {
        /* Load the UI */
        webkit_web_view_load_uri(webview, SERVER_URL);
    } else {
        /* Show error */
        const char *error_html =
            "<!DOCTYPE html><html><head><meta charset='utf-8'>"
            "<style>body { font-family: system-ui; padding: 2em; text-align: center; }"
            "h1 { color: #e01b24; }</style></head><body>"
            "<h1>⚠ Failed to Start Server</h1>"
            "<p>Could not start the Cyberspace server.</p>"
            "<p>Please ensure Chez Scheme is installed.</p>"
            "</body></html>";
        webkit_web_view_load_html(webview, error_html, NULL);
    }

    /* Show window */
    gtk_window_present(GTK_WINDOW(main_window));
}

/* Application shutdown handler */
static void on_shutdown(GApplication *app, gpointer user_data) {
    g_debug("Application shutting down");
    stop_server();
}

/* Main entry point */
int main(int argc, char *argv[]) {
    AdwApplication *app;
    int status;

    /* Create application */
    app = adw_application_new(APP_ID, G_APPLICATION_DEFAULT_FLAGS);

    /* Connect signals */
    g_signal_connect(app, "activate", G_CALLBACK(on_activate), NULL);
    g_signal_connect(app, "shutdown", G_CALLBACK(on_shutdown), NULL);

    /* Run application */
    status = g_application_run(G_APPLICATION(app), argc, argv);

    /* Cleanup */
    g_object_unref(app);

    return status;
}
