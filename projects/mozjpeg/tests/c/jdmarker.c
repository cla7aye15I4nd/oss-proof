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

static void susp_init_source(j_decompress_ptr cinfo) { (void)cinfo; }
static boolean susp_fill_input_buffer(j_decompress_ptr cinfo) { (void)cinfo; return FALSE; }
static void susp_skip_input_data(j_decompress_ptr cinfo, long num_bytes) { (void)cinfo; (void)num_bytes; }
static void susp_term_source(j_decompress_ptr cinfo) { (void)cinfo; }

static int hex_val(char c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return -1;
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
        } else if (strcmp(tok[0], "resync") == 0 && nt == 5) {
            int unread = (int)parse_i(tok[1]);
            int desired = (int)parse_i(tok[2]);
            int fill_mode = (int)parse_i(tok[3]);
            const char *hex = tok[4];
            size_t nbytes = 0;
            unsigned char buf[256];
            if (strcmp(hex, "-") != 0) {
                size_t slen = strlen(hex);
                if (slen % 2 != 0 || slen / 2 > sizeof(buf)) { bad = 1; continue; }
                nbytes = slen / 2;
                for (size_t i = 0; i < nbytes; i++) {
                    int hi = hex_val(hex[2 * i]), lo = hex_val(hex[2 * i + 1]);
                    if (hi < 0 || lo < 0) { bad = 1; break; }
                    buf[i] = (unsigned char)((hi << 4) | lo);
                }
            }
            struct jpeg_decompress_struct cinfo;
            struct err_env jerr;
            struct jpeg_source_mgr susp_src;
            unsigned char dummy[1] = {0};
            memset(&cinfo, 0, sizeof(cinfo));
            cinfo.err = jpeg_std_error(&jerr.pub);
            jerr.pub.error_exit = test_error_exit;
            if (setjmp(jerr.jmp)) {
                printf("err %d %d\n", jerr.pub.msg_code, jerr.pub.msg_parm.i[0]);
                jpeg_destroy_decompress(&cinfo);
                continue;
            }
            jpeg_create_decompress(&cinfo);
            if (fill_mode == 1) {
                memset(&susp_src, 0, sizeof(susp_src));
                susp_src.init_source = susp_init_source;
                susp_src.fill_input_buffer = susp_fill_input_buffer;
                susp_src.skip_input_data = susp_skip_input_data;
                susp_src.resync_to_restart = jpeg_resync_to_restart;
                susp_src.term_source = susp_term_source;
                susp_src.bytes_in_buffer = nbytes;
                susp_src.next_input_byte = nbytes > 0 ? buf : dummy;
                cinfo.src = &susp_src;
            } else {
                if (nbytes > 0) {
                    jpeg_mem_src(&cinfo, buf, nbytes);
                } else {
                    jpeg_mem_src(&cinfo, dummy, 1);
                    cinfo.src->bytes_in_buffer = 0;
                    cinfo.src->next_input_byte = dummy;
                }
            }
            cinfo.unread_marker = unread;
            boolean ret = jpeg_resync_to_restart(&cinfo, desired);
            printf("resync ret=%d unread=%d bib=%zu rem=", ret, cinfo.unread_marker, cinfo.src->bytes_in_buffer);
            if (cinfo.src->bytes_in_buffer == 0) {
                putchar('-');
            } else {
                for (size_t i = 0; i < cinfo.src->bytes_in_buffer; i++) {
                    printf("%02x", cinfo.src->next_input_byte[i]);
                }
            }
            printf(" warn=%ld disc=%u code=%d p0=%d p1=%d\n",
                   jerr.pub.num_warnings,
                   cinfo.marker->discarded_bytes,
                   jerr.pub.msg_code,
                   jerr.pub.msg_parm.i[0],
                   jerr.pub.msg_parm.i[1]);
            if (fill_mode == 1) cinfo.src = NULL;
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
