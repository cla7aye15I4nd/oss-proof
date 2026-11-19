#include "common.h"
#include "jpeglib.h"

int main(void) {
    char *line = NULL;
    size_t cap = 0;
    int bad = 0;
    while (getline(&line, &cap, stdin) >= 0) {
        char *tok[8];
        int nt = split(line, tok, 8);
        if (nt == 0) continue;
        const char *fn = tok[0];
        if (strcmp(fn, "jpeg_std_error") == 0 && nt == 4) {
            struct jpeg_error_mgr jerr;
            memset(&jerr, 0x55, sizeof(jerr));
            jerr.trace_level = (int)parse_i(tok[1]);
            jerr.num_warnings = (long)parse_i(tok[2]);
            int idx = (int)parse_i(tok[3]);
            struct jpeg_error_mgr *ret = jpeg_std_error(&jerr);
            const char *msg = "";
            if (idx >= 0 && idx <= ret->last_jpeg_message && ret->jpeg_message_table) {
                msg = ret->jpeg_message_table[idx] ? ret->jpeg_message_table[idx] : "";
            }
            printf("%d %ld %d %d %s\n",
                   ret->msg_code,
                   ret->num_warnings,
                   ret->trace_level,
                   ret->last_jpeg_message,
                   msg);
        } else {
            fprintf(stderr, "unknown function or wrong arity: %s\n", fn);
            printf("BADINPUT\n");
            bad = 1;
        }
    }
    free(line);
    return bad;
}
