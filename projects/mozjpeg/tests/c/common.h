/* Shared parsing helpers for mozjpeg C differential-test drivers. */
#ifndef DIFFTEST_COMMON_H
#define DIFFTEST_COMMON_H

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define UNUSED __attribute__((unused))

UNUSED static unsigned long long parse_u(const char *s) {
    char *e; errno = 0;
    unsigned long long v = strtoull(s, &e, 10);
    if (*s == '\0' || *e != '\0' || errno || *s == '-') {
        fprintf(stderr, "bad unsigned %s\n", s);
        exit(2);
    }
    return v;
}

UNUSED static long long parse_i(const char *s) {
    char *e; errno = 0;
    long long v = strtoll(s, &e, 10);
    if (*s == '\0' || *e != '\0' || errno) {
        fprintf(stderr, "bad signed %s\n", s);
        exit(2);
    }
    return v;
}

UNUSED static int split(char *line, char **tok, int max_tok) {
    char *save;
    int nt = 0;
    for (char *t = strtok_r(line, " \t\r\n", &save); t && nt < max_tok;
         t = strtok_r(NULL, " \t\r\n", &save)) {
        tok[nt++] = t;
    }
    return nt;
}

#endif
