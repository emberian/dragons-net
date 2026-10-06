/* SPDX-License-Identifier: AGPL-3.0-or-later
 * Points of failure of the host's test build (decision 0005), as libfiu's fiu-local.h has them:
 * built with FIU_ENABLE and libfiu, a point a test enables fails with the error number it was
 * enabled with; built without, a point is no code. */
#ifndef DN_FAULTS_H
#define DN_FAULTS_H
#include <errno.h>
#include <stdint.h>
#ifdef FIU_ENABLE
#include <fiu.h>
#else
#define fiu_fail(name) ((void)(name), 0)
#define fiu_failinfo() NULL
#endif

/* Whether the point `name` fails now, errno then set to the number it was enabled with. */
#define DN_FAULT(name) (fiu_fail(name) ? (errno = (int)(intptr_t)fiu_failinfo(), 1) : 0)

/* The number the point `name` was enabled with, if it is enabled now. */
#define DN_FAULT_INFO(name, info) (fiu_fail(name) ? ((info) = (uint64_t)(uintptr_t)fiu_failinfo(), 1) : 0)

#endif
