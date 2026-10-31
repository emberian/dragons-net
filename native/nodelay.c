// SPDX-License-Identifier: AGPL-3.0-or-later
/*
 * Loaded with LD_PRELOAD, sets TCP_NODELAY on every connection a server accepts. INN's reader
 * writes a reply in two calls without it, and so waits for a delayed acknowledgement once a
 * connection asks for more than some 25 replies a second; scripts/bench.py measures INN with and
 * without this. A socket that is not TCP refuses the option, which is ignored.
 */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <sys/socket.h>

static void no_delay(int fd) {
    int one = 1;
    if (fd >= 0) setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof one);
}

int accept(int fd, struct sockaddr *address, socklen_t *length) {
    static int (*real)(int, struct sockaddr *, socklen_t *);
    if (!real) real = (int (*)(int, struct sockaddr *, socklen_t *))dlsym(RTLD_NEXT, "accept");
    int got = real(fd, address, length);
    no_delay(got);
    return got;
}

int accept4(int fd, struct sockaddr *address, socklen_t *length, int flags) {
    static int (*real)(int, struct sockaddr *, socklen_t *, int);
    if (!real) real = (int (*)(int, struct sockaddr *, socklen_t *, int))dlsym(RTLD_NEXT, "accept4");
    int got = real(fd, address, length, flags);
    no_delay(got);
    return got;
}
