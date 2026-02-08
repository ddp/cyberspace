/* fuse-bridge.c - FUSE FFI Bridge for Chez Scheme
 *
 * Passthrough filesystem for Cyberspace wormholes.
 *
 * Compile (macOS with FUSE-T):
 *   cc -shared -fPIC -o fuse-bridge.dylib fuse-bridge.c \
 *      -I/usr/local/include/fuse -L/usr/local/lib -lfuse-t -D_FILE_OFFSET_BITS=64
 *
 * Compile (macOS with macFUSE):
 *   cc -shared -fPIC -o fuse-bridge.dylib fuse-bridge.c \
 *      -I/usr/local/include/osxfuse -L/usr/local/lib -losxfuse -D_FILE_OFFSET_BITS=64
 *
 * Compile (Linux):
 *   cc -shared -fPIC -o fuse-bridge.so fuse-bridge.c \
 *      $(pkg-config fuse --cflags --libs) -D_FILE_OFFSET_BITS=64
 *
 * Copyright (c) 2026 Yoyodyne. See LICENSE.
 */

#define _FILE_OFFSET_BITS 64

#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <fcntl.h>
#include <unistd.h>
#include <dirent.h>
#include <stdio.h>
#include <sys/stat.h>
#include <sys/types.h>

/* Check for FUSE availability */
#if defined(__has_include)
  #if __has_include(<fuse.h>)
    #define FUSE_USE_VERSION 26
    #include <fuse.h>
    #define HAVE_FUSE 1
  #else
    #define HAVE_FUSE 0
  #endif
#else
  /* Try to include fuse.h; will fail at compile time if not available */
  #define FUSE_USE_VERSION 26
  #include <fuse.h>
  #define HAVE_FUSE 1
#endif

/* Stat buffer for returning file attributes from Scheme */
static struct stat fuse_stat_buffer;

void init_stat_buffer(void) {
    memset(&fuse_stat_buffer, 0, sizeof(struct stat));
}

void set_stat_mode(int mode)     { fuse_stat_buffer.st_mode = mode; }
void set_stat_nlink(int nlink)   { fuse_stat_buffer.st_nlink = nlink; }
void set_stat_size(long long sz) { fuse_stat_buffer.st_size = sz; }
void set_stat_uid(int uid)       { fuse_stat_buffer.st_uid = uid; }
void set_stat_gid(int gid)       { fuse_stat_buffer.st_gid = gid; }
void set_stat_atime(long long t) { fuse_stat_buffer.st_atime = t; }
void set_stat_mtime(long long t) { fuse_stat_buffer.st_mtime = t; }
void set_stat_ctime(long long t) { fuse_stat_buffer.st_ctime = t; }

int fuse_bridge_available(void) {
#if HAVE_FUSE
    return 1;
#else
    return 0;
#endif
}

#if HAVE_FUSE

/*
 * Passthrough filesystem: mirrors a source directory.
 * Scheme sets the source path before mount.
 */
static char source_path[4096] = "";

void set_source_path(const char *path) {
    strncpy(source_path, path, sizeof(source_path) - 1);
    source_path[sizeof(source_path) - 1] = '\0';
}

static void full_path(char *dest, const char *path, size_t size) {
    snprintf(dest, size, "%s%s", source_path, path);
}

/* FUSE operations - passthrough to source directory */

static int cs_getattr(const char *path, struct stat *stbuf) {
    char fpath[4096];
    full_path(fpath, path, sizeof(fpath));
    int res = lstat(fpath, stbuf);
    return res == -1 ? -errno : 0;
}

static int cs_readdir(const char *path, void *buf, fuse_fill_dir_t filler,
                      off_t offset, struct fuse_file_info *fi) {
    (void) offset;
    (void) fi;
    char fpath[4096];
    full_path(fpath, path, sizeof(fpath));

    DIR *dp = opendir(fpath);
    if (dp == NULL) return -errno;

    struct dirent *de;
    while ((de = readdir(dp)) != NULL) {
        filler(buf, de->d_name, NULL, 0);
    }
    closedir(dp);
    return 0;
}

static int cs_open(const char *path, struct fuse_file_info *fi) {
    char fpath[4096];
    full_path(fpath, path, sizeof(fpath));
    int fd = open(fpath, fi->flags);
    if (fd == -1) return -errno;
    close(fd);
    return 0;
}

static int cs_read(const char *path, char *buf, size_t size, off_t offset,
                   struct fuse_file_info *fi) {
    (void) fi;
    char fpath[4096];
    full_path(fpath, path, sizeof(fpath));
    int fd = open(fpath, O_RDONLY);
    if (fd == -1) return -errno;
    int res = pread(fd, buf, size, offset);
    close(fd);
    return res == -1 ? -errno : res;
}

static int cs_write(const char *path, const char *buf, size_t size, off_t offset,
                    struct fuse_file_info *fi) {
    (void) fi;
    char fpath[4096];
    full_path(fpath, path, sizeof(fpath));
    int fd = open(fpath, O_WRONLY);
    if (fd == -1) return -errno;
    int res = pwrite(fd, buf, size, offset);
    close(fd);
    return res == -1 ? -errno : res;
}

static int cs_create(const char *path, mode_t mode, struct fuse_file_info *fi) {
    (void) fi;
    char fpath[4096];
    full_path(fpath, path, sizeof(fpath));
    int fd = creat(fpath, mode);
    if (fd == -1) return -errno;
    close(fd);
    return 0;
}

static int cs_unlink(const char *path) {
    char fpath[4096];
    full_path(fpath, path, sizeof(fpath));
    return unlink(fpath) == -1 ? -errno : 0;
}

static int cs_mkdir(const char *path, mode_t mode) {
    char fpath[4096];
    full_path(fpath, path, sizeof(fpath));
    return mkdir(fpath, mode) == -1 ? -errno : 0;
}

static int cs_rmdir(const char *path) {
    char fpath[4096];
    full_path(fpath, path, sizeof(fpath));
    return rmdir(fpath) == -1 ? -errno : 0;
}

static int cs_truncate(const char *path, off_t size) {
    char fpath[4096];
    full_path(fpath, path, sizeof(fpath));
    return truncate(fpath, size) == -1 ? -errno : 0;
}

static int cs_rename(const char *from, const char *to) {
    char ffrom[4096], fto[4096];
    full_path(ffrom, from, sizeof(ffrom));
    full_path(fto, to, sizeof(fto));
    return rename(ffrom, fto) == -1 ? -errno : 0;
}

static struct fuse_operations cyberspace_ops = {
    .getattr  = cs_getattr,
    .readdir  = cs_readdir,
    .open     = cs_open,
    .read     = cs_read,
    .write    = cs_write,
    .create   = cs_create,
    .unlink   = cs_unlink,
    .mkdir    = cs_mkdir,
    .rmdir    = cs_rmdir,
    .truncate = cs_truncate,
    .rename   = cs_rename,
};

static volatile int fuse_running = 0;

/* Run FUSE - call from Scheme, blocks until unmount */
int run_fuse(const char *mountpoint) {
    char *argv[] = {"cyberspace", (char*)mountpoint, "-f", NULL};
    int argc = 3;
    fuse_running = 1;
    int ret = fuse_main(argc, argv, &cyberspace_ops, NULL);
    fuse_running = 0;
    return ret;
}

int is_fuse_running(void) {
    return fuse_running;
}

#else /* !HAVE_FUSE */

void set_source_path(const char *path) { (void)path; }
int run_fuse(const char *mountpoint) { (void)mountpoint; return -1; }
int is_fuse_running(void) { return 0; }

#endif /* HAVE_FUSE */
