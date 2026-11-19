#include "common.h"
#include "jpeglib.h"
#include "jpegint.h"
#include <setjmp.h>

typedef struct {
    struct jpeg_marker_reader pub;
    jpeg_marker_parser_method process_COM;
    jpeg_marker_parser_method process_APPn[16];
    unsigned int length_limit_COM;
    unsigned int length_limit_APPn[16];
} my_marker_reader_view;

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
        if (strcmp(tok[0], "jpeg_save_markers") == 0 && nt == 3) {
            int marker_code = (int)parse_i(tok[1]);
            unsigned int length_limit = (unsigned int)parse_u(tok[2]);
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
            jpeg_save_markers(&cinfo, marker_code, length_limit);
            my_marker_reader_view *mr = (my_marker_reader_view *)cinfo.marker;
            printf("ok com=%u app0=%u app1=%u app2=%u app13=%u app14=%u app15=%u\n",
                   mr->length_limit_COM,
                   mr->length_limit_APPn[0],
                   mr->length_limit_APPn[1],
                   mr->length_limit_APPn[2],
                   mr->length_limit_APPn[13],
                   mr->length_limit_APPn[14],
                   mr->length_limit_APPn[15]);
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
