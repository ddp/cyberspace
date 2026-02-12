/*
 * metadata-bridge.c - File Metadata FFI bridge for Chez Scheme (Darwin)
 *
 * Provides extended attributes, BSD flags, and ACL operations.
 * Darwin-specific; other platforms will need separate implementations.
 *
 * Build: cc -shared -o libmetadata-bridge.dylib metadata-bridge.c  (macOS)
 */

#include <sys/types.h>
#include <sys/stat.h>
#include <sys/xattr.h>
#include <sys/acl.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>

/* Get list of xattr names, return as null-separated string.
 * Caller must free the returned buffer. */
char* metadata_xattr_list(const char* path, int* out_len) {
    ssize_t len = listxattr(path, NULL, 0, XATTR_NOFOLLOW);
    if (len <= 0) {
        *out_len = 0;
        return NULL;
    }
    char* buf = malloc(len);
    if (!buf) {
        *out_len = 0;
        return NULL;
    }
    ssize_t actual = listxattr(path, buf, len, XATTR_NOFOLLOW);
    if (actual < 0) {
        free(buf);
        *out_len = 0;
        return NULL;
    }
    *out_len = (int)actual;
    return buf;
}

/* Get single xattr value.
 * Caller must free the returned buffer. */
char* metadata_xattr_get(const char* path, const char* name, int* out_len) {
    ssize_t len = getxattr(path, name, NULL, 0, 0, XATTR_NOFOLLOW);
    if (len < 0) {
        *out_len = 0;
        return NULL;
    }
    if (len == 0) {
        *out_len = 0;
        return strdup("");
    }
    char* buf = malloc(len + 1);
    if (!buf) {
        *out_len = 0;
        return NULL;
    }
    ssize_t actual = getxattr(path, name, buf, len, 0, XATTR_NOFOLLOW);
    if (actual < 0) {
        free(buf);
        *out_len = 0;
        return NULL;
    }
    buf[actual] = '\0';
    *out_len = (int)actual;
    return buf;
}

/* Set xattr value */
int metadata_xattr_set(const char* path, const char* name,
                       const char* value, int len) {
    return setxattr(path, name, value, len, 0, XATTR_NOFOLLOW);
}

/* Remove xattr */
int metadata_xattr_remove(const char* path, const char* name) {
    return removexattr(path, name, XATTR_NOFOLLOW);
}

/* Get BSD file flags from stat */
unsigned int metadata_get_flags(const char* path) {
    struct stat st;
    if (lstat(path, &st) < 0) return 0;
    return st.st_flags;
}

/* Set BSD file flags */
int metadata_set_flags(const char* path, unsigned int flags) {
    return chflags(path, flags);
}

/* Get ACL as text (caller must free) */
char* metadata_acl_get_text(const char* path) {
    acl_t acl = acl_get_file(path, ACL_TYPE_EXTENDED);
    if (!acl) return NULL;
    char* text = acl_to_text(acl, NULL);
    acl_free(acl);
    if (!text) return NULL;
    char* result = strdup(text);
    acl_free(text);
    return result;
}

/* Set ACL from text */
int metadata_acl_set_text(const char* path, const char* text) {
    acl_t acl = acl_from_text(text);
    if (!acl) return -1;
    int result = acl_set_file(path, ACL_TYPE_EXTENDED, acl);
    acl_free(acl);
    return result;
}

/* Free a buffer allocated by this library */
void metadata_free(void* ptr) {
    free(ptr);
}
