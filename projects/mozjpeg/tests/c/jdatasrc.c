#include "common.h"
#include "jpeglib.h"
#include <setjmp.h>
#include <stdint.h>

struct err_env {
    struct jpeg_error_mgr pub;
    jmp_buf jmp;
};

static void test_error_exit(j_common_ptr cinfo) {
    struct err_env *env = (struct err_env *)cinfo->err;
    longjmp(env->jmp, 1);
}

static void foreign_init(j_decompress_ptr cinfo) { (void)cinfo; }
static boolean foreign_fill(j_decompress_ptr cinfo) { (void)cinfo; return FALSE; }
static void foreign_skip(j_decompress_ptr cinfo, long n) { (void)cinfo; (void)n; }
static void foreign_term(j_decompress_ptr cinfo) { (void)cinfo; }

int main(void) {
    char *line = NULL;
    size_t cap = 0;
    int bad = 0;
    unsigned char buf[64];
    for (int i = 0; i < 64; i++) buf[i] = (unsigned char)((i * 17 + 3) & 0xff);

    while (getline(&line, &cap, stdin) >= 0) {
        char *tok[8];
        int nt = split(line, tok, 8);
        if (nt == 0) continue;
        if (strcmp(tok[0], "mem_src") == 0 && nt == 4) {
            int nonnull = (int)parse_i(tok[1]);
            unsigned long insize = (unsigned long)parse_u(tok[2]);
            int preset = (int)parse_i(tok[3]);
            struct jpeg_decompress_struct cinfo;
            struct err_env jerr;
            struct jpeg_source_mgr foreign_src;
            memset(&cinfo, 0, sizeof(cinfo));
            cinfo.err = jpeg_std_error(&jerr.pub);
            jerr.pub.error_exit = test_error_exit;
            if (setjmp(jerr.jmp)) {
                printf("err %d\n", jerr.pub.msg_code);
                if (preset == 2) cinfo.src = NULL;
                jpeg_destroy_decompress(&cinfo);
                continue;
            }
            jpeg_create_decompress(&cinfo);
            if (preset == 1) {
                jpeg_mem_src(&cinfo, buf, 7);
            } else if (preset == 2) {
                memset(&foreign_src, 0, sizeof(foreign_src));
                foreign_src.init_source = foreign_init;
                foreign_src.fill_input_buffer = foreign_fill;
                foreign_src.skip_input_data = foreign_skip;
                foreign_src.resync_to_restart = jpeg_resync_to_restart;
                foreign_src.term_source = foreign_term;
                cinfo.src = &foreign_src;
            }
            jpeg_mem_src(&cinfo, nonnull ? buf : NULL, insize);
            (*cinfo.src->init_source)(&cinfo);
            printf("ok bib=%zu samebuf=%d\n",
                   cinfo.src->bytes_in_buffer,
                   cinfo.src->next_input_byte == buf ? 1 : 0);
            (*cinfo.src->term_source)(&cinfo);
            if (preset == 2) cinfo.src = NULL;
            jpeg_destroy_decompress(&cinfo);
        } else if (strcmp(tok[0], "skip") == 0 && nt == 4) {
            unsigned long insize = (unsigned long)parse_u(tok[1]);
            long n1 = (long)parse_i(tok[2]);
            long n2 = (long)parse_i(tok[3]);
            if (insize == 0 || insize > sizeof(buf)) { bad = 1; continue; }
            struct jpeg_decompress_struct cinfo;
            struct err_env jerr;
            memset(&cinfo, 0, sizeof(cinfo));
            cinfo.err = jpeg_std_error(&jerr.pub);
            jerr.pub.error_exit = test_error_exit;
            if (setjmp(jerr.jmp)) {
                printf("err %d\n", jerr.pub.msg_code);
                jpeg_destroy_decompress(&cinfo);
                continue;
            }
            jpeg_create_decompress(&cinfo);
            jpeg_mem_src(&cinfo, buf, insize);
            (*cinfo.src->skip_input_data)(&cinfo, n1);
            (*cinfo.src->skip_input_data)(&cinfo, n2);
            int head = cinfo.src->bytes_in_buffer > 0 ? (int)cinfo.src->next_input_byte[0] : -1;
            printf("skip bib=%zu warn=%ld code=%d head=%d\n",
                   cinfo.src->bytes_in_buffer, jerr.pub.num_warnings, jerr.pub.msg_code, head);
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
