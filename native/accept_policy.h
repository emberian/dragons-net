/* SPDX-License-Identifier: AGPL-3.0-or-later
 * How an accept() failure is treated. */
#ifndef DN_ACCEPT_POLICY_H
#define DN_ACCEPT_POLICY_H
#include <errno.h>

enum dn_accept_action {
    DN_ACCEPT_RETRY,  /* nothing was waiting, or the peer went away: try again at once */
    DN_ACCEPT_PAUSE,  /* out of a resource: keep serving, leave the listener alone a while */
    DN_ACCEPT_FATAL   /* the listener itself cannot work */
};

/* accept(2) hands the new socket's already-pending network errors back as its own, and
 * says to retry those like EAGAIN. Resource exhaustion is temporary as well, but retrying
 * at once would spin. Only a listener that cannot work at all ends the server, and an
 * error this list does not name pauses rather than stops: an unknown failure is not worth
 * dropping the connections already being served. */
static inline enum dn_accept_action dn_accept_action(int code) {
    switch (code) {
    case EAGAIN:
#if defined(EWOULDBLOCK) && EWOULDBLOCK != EAGAIN
    case EWOULDBLOCK:
#endif
    case EINTR: case ECONNABORTED: case EPERM: case EPROTO:
    case ENETDOWN: case ENOPROTOOPT: case EHOSTDOWN: case ENONET:
    case EHOSTUNREACH: case ENETUNREACH: case EOPNOTSUPP:
    case ETIMEDOUT: case ECONNRESET:
        return DN_ACCEPT_RETRY;
    case EBADF: case EINVAL: case ENOTSOCK: case EFAULT:
        return DN_ACCEPT_FATAL;
    default:
        return DN_ACCEPT_PAUSE;
    }
}

#endif
