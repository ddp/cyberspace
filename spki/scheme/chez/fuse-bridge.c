/*
 * fuse-bridge.c - FUSE passthrough filesystem bridge for Cyberspace
 *
 * Provides a passthrough FUSE filesystem where all operations are
 * forwarded to a configurable source directory. Used by wormhole.sls.
 *
 * Build (requires FUSE-T or macFUSE):
 *   cc -shared -o libfuse-bridge.dylib fuse-bridge.c \
 *      -I/usr/local/include/fuse -L/usr/local/lib -lfuse-t
 *
 * Or with pkg-config:
 *   cc -shared -o libfuse-bridge.dylib fuse-bridge.c $(pkg-config fuse --cflags --libs)
 *
 * If FUSE is not installed, build with stubs:
 *   cc -shared -o libfuse-bridge.dylib fuse-bridge.c -DNO_FUSE
 */

#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/types.h>

#ifndef NO_FUSE

#define FUSE_USE_VERSION 26

#ifdef __APPLE__
#include <fuse.h>
#else
#include <fuse.h>
#endif

#include <dirent.h>

/* Source path for passthrough */
static char source_path[4096] = "";

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
    int res = (int)pread(fd, buf, size, offset);
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
    int res = (int)pwrite(fd, buf, size, offset);
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

#endif /* !NO_FUSE */

/* Stat buffer for returning file attributes to Scheme */
static struct stat fuse_stat_buffer;

/*
 * Public API - called from Scheme via foreign-procedure
 */

void fuse_set_source_path(const char *path) {
#ifndef NO_FUSE
    strncpy(source_path, path, sizeof(source_path) - 1);
    source_path[sizeof(source_path) - 1] = '\0';
#else
    (void)path;
#endif
}

int fuse_run_mount(const char *mountpoint) {
#ifndef NO_FUSE
    char *argv[] = {"cyberspace", (char*)mountpoint, "-f", NULL};
    int argc = 3;
    fuse_running = 1;
    int ret = fuse_main(argc, argv, &cyberspace_ops, NULL);
    fuse_running = 0;
    return ret;
#else
    (void)mountpoint;
    return -1;
#endif
}

int fuse_is_running(void) {
#ifndef NO_FUSE
    return fuse_running;
#else
    return 0;
#endif
}

void fuse_init_stat_buffer(void) {
    memset(&fuse_stat_buffer, 0, sizeof(struct stat));
}

void fuse_set_stat_mode(int mode) { fuse_stat_buffer.st_mode = mode; }
void fuse_set_stat_nlink(int nlink) { fuse_stat_buffer.st_nlink = nlink; }
void fuse_set_stat_size(long size) { fuse_stat_buffer.st_size = size; }
void fuse_set_stat_uid(int uid) { fuse_stat_buffer.st_uid = uid; }
void fuse_set_stat_gid(int gid) { fuse_stat_buffer.st_gid = gid; }
void fuse_set_stat_atime(long t) { fuse_stat_buffer.st_atime = t; }
void fuse_set_stat_mtime(long t) { fuse_stat_buffer.st_mtime = t; }
void fuse_set_stat_ctime(long t) { fuse_stat_buffer.st_ctime = t; }
