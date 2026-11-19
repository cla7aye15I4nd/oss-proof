#include "common.h"
#include "jpeglib.h"
#include "jpegint.h"
#include <setjmp.h>

struct err_env {
    struct jpeg_error_mgr pub;
    jmp_buf jmp;
};

static void test_error_exit(j_common_ptr cinfo) {
    struct err_env *env = (struct err_env *)cinfo->err;
    longjmp(env->jmp, 1);
}

int main(void) {
    char *line = NULL;
    size_t cap = 0;
    int bad = 0;
    while (getline(&line, &cap, stdin) >= 0) {
        char *tok[8];
        int nt = split(line, tok, 8);
        if (nt == 0) continue;
        if (strcmp(tok[0], "create") == 0 && nt == 3) {
            int ver = (int)parse_i(tok[1]);
            size_t sz = (size_t)parse_u(tok[2]);
            struct jpeg_decompress_struct cinfo;
            struct err_env jerr;
            memset(&cinfo, 0x5a, sizeof(cinfo));
            cinfo.err = jpeg_std_error(&jerr.pub);
            jerr.pub.error_exit = test_error_exit;
            if (setjmp(jerr.jmp)) {
                int code = jerr.pub.msg_code;
                int p0 = jerr.pub.msg_parm.i[0];
                int p1 = jerr.pub.msg_parm.i[1];
                jpeg_destroy_decompress(&cinfo);
                printf("err code=%d p0=%d p1=%d after_mn=%d\n", code, p0, p1, cinfo.mem == NULL ? 1 : 0);
                continue;
            }
            jpeg_CreateDecompress(&cinfo, ver, sz);
            int st = cinfo.global_state;
            int dp = cinfo.data_precision;
            int isd = cinfo.is_decompressor;
            int mn = cinfo.mem == NULL ? 1 : 0;
            int mrn = cinfo.marker == NULL ? 1 : 0;
            int icn = cinfo.inputctl == NULL ? 1 : 0;
            int man = cinfo.master == NULL ? 1 : 0;
            int sn = cinfo.src == NULL ? 1 : 0;
            jpeg_destroy_decompress(&cinfo);
            printf("ok state=%d dp=%d isd=%d mn=%d mrn=%d icn=%d man=%d sn=%d after_mn=%d\n",
                   st, dp, isd, mn, mrn, icn, man, sn, cinfo.mem == NULL ? 1 : 0);
        } else if (strcmp(tok[0], "abort_destroy") == 0 && nt == 2) {
            int st = (int)parse_i(tok[1]);
            struct jpeg_decompress_struct cinfo;
            struct err_env jerr;
            memset(&cinfo, 0, sizeof(cinfo));
            cinfo.err = jpeg_std_error(&jerr.pub);
            jerr.pub.error_exit = test_error_exit;
            jpeg_create_decompress(&cinfo);
            cinfo.global_state = st;
            jpeg_abort_decompress(&cinfo);
            int after_st = cinfo.global_state;
            jpeg_destroy_decompress(&cinfo);
            printf("abort state=%d after_mn=%d\n", after_st, cinfo.mem == NULL ? 1 : 0);
        } else if (strcmp(tok[0], "input_complete") == 0 && nt == 3) {
            int st = (int)parse_i(tok[1]);
            boolean eoi = (boolean)parse_i(tok[2]);
            struct jpeg_decompress_struct cinfo;
            struct err_env jerr;
            memset(&cinfo, 0, sizeof(cinfo));
            cinfo.err = jpeg_std_error(&jerr.pub);
            jerr.pub.error_exit = test_error_exit;
            if (setjmp(jerr.jmp)) {
                printf("err %d %d\n", jerr.pub.msg_code, jerr.pub.msg_parm.i[0]);
                jpeg_destroy_decompress(&cinfo);
                continue;
            }
            jpeg_create_decompress(&cinfo);
            cinfo.global_state = st;
            cinfo.inputctl->eoi_reached = eoi;
            boolean r = jpeg_input_complete(&cinfo);
            printf("ic %d\n", r);
            jpeg_destroy_decompress(&cinfo);
        } else if (strcmp(tok[0], "has_multiple_scans") == 0 && nt == 3) {
            int st = (int)parse_i(tok[1]);
            boolean hms = (boolean)parse_i(tok[2]);
            struct jpeg_decompress_struct cinfo;
            struct err_env jerr;
            memset(&cinfo, 0, sizeof(cinfo));
            cinfo.err = jpeg_std_error(&jerr.pub);
            jerr.pub.error_exit = test_error_exit;
            if (setjmp(jerr.jmp)) {
                printf("err %d %d\n", jerr.pub.msg_code, jerr.pub.msg_parm.i[0]);
                jpeg_destroy_decompress(&cinfo);
                continue;
            }
            jpeg_create_decompress(&cinfo);
            cinfo.global_state = st;
            cinfo.inputctl->has_multiple_scans = hms;
            boolean r = jpeg_has_multiple_scans(&cinfo);
            printf("hms %d\n", r);
            jpeg_destroy_decompress(&cinfo);
        } else {
            fprintf(stderr, "unknown command: %s\n", tok[0]);
            printf("BADINPUT\n");
            bad = 1;
        }
    }
    free(line);
    return bad;
}
