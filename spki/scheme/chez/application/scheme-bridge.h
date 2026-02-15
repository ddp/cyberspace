/*
 * scheme-bridge.h - Chez Scheme native bridge for macOS
 *
 * Provides C/Objective-C interface to Chez Scheme evaluation.
 */

#ifndef SCHEME_BRIDGE_H
#define SCHEME_BRIDGE_H

#include <stdbool.h>

/* Initialize the Scheme interpreter */
bool scheme_init(int argc, char **argv);

/* Evaluate a Scheme expression and return the result as a string */
char* scheme_eval(const char *expr);

/* Free a result string returned by scheme_eval */
void scheme_free_result(char *result);

/* Shutdown the Scheme interpreter */
void scheme_cleanup(void);

/* Show About dialog (called from Scheme) */
void scheme_show_about(void);

#endif /* SCHEME_BRIDGE_H */
