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

static int parse_hex_buf(const char *hex, unsigned char *buf, size_t cap, size_t *out_n) {
    if (strcmp(hex, "-") == 0) {
        *out_n = 0;
        return 1;
    }
    size_t slen = strlen(hex);
    if (slen % 2 != 0 || slen / 2 > cap) return 0;
    size_t n = slen / 2;
    for (size_t i = 0; i < n; i++) {
        int hi = hex_val(hex[2 * i]), lo = hex_val(hex[2 * i + 1]);
        if (hi < 0 || lo < 0) return 0;
        buf[i] = (unsigned char)((hi << 4) | lo);
    }
    *out_n = n;
    return 1;
}

static void setup_src(j_decompress_ptr cinfo, int fill_mode, struct jpeg_source_mgr *susp_src,
                      unsigned char *buf, size_t nbytes, unsigned char *dummy) {
    if (fill_mode == 1) {
        memset(susp_src, 0, sizeof(*susp_src));
        susp_src->init_source = susp_init_source;
        susp_src->fill_input_buffer = susp_fill_input_buffer;
        susp_src->skip_input_data = susp_skip_input_data;
        susp_src->resync_to_restart = jpeg_resync_to_restart;
        susp_src->term_source = susp_term_source;
        susp_src->bytes_in_buffer = nbytes;
        susp_src->next_input_byte = nbytes > 0 ? buf : dummy;
        cinfo->src = susp_src;
    } else if (nbytes > 0) {
        jpeg_mem_src(cinfo, buf, nbytes);
    } else {
        jpeg_mem_src(cinfo, dummy, 1);
        cinfo->src->bytes_in_buffer = 0;
        cinfo->src->next_input_byte = dummy;
    }
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
        } else if (strcmp(tok[0], "read_header") == 0 && nt == 5) {
            boolean req = (boolean)parse_i(tok[1]);
            int fill_mode = (int)parse_i(tok[2]);
            unsigned int save_mask = (unsigned int)parse_u(tok[3]);
            unsigned char buf[4096];
            unsigned char dummy[1] = {0};
            size_t nbytes = 0;
            if (!parse_hex_buf(tok[4], buf, sizeof(buf), &nbytes)) { bad = 1; continue; }
            struct jpeg_decompress_struct cinfo;
            struct err_env jerr;
            struct jpeg_source_mgr susp_src;
            memset(&cinfo, 0, sizeof(cinfo));
            cinfo.err = jpeg_std_error(&jerr.pub);
            jerr.pub.error_exit = test_error_exit;
            if (setjmp(jerr.jmp)) {
                printf("err %d %d\n", jerr.pub.msg_code, jerr.pub.msg_parm.i[0]);
                if (fill_mode == 1) cinfo.src = NULL;
                jpeg_destroy_decompress(&cinfo);
                continue;
            }
            jpeg_create_decompress(&cinfo);
            setup_src(&cinfo, fill_mode, &susp_src, buf, nbytes, dummy);
            if (save_mask & 1u) jpeg_save_markers(&cinfo, 0xE0, 65535);
            if (save_mask & 2u) jpeg_save_markers(&cinfo, 0xFE, 8);
            int ret = jpeg_read_header(&cinfo, req);
            int nsaved = 0;
            for (jpeg_saved_marker_ptr p = cinfo.marker_list; p != NULL; p = p->next) nsaved++;
            int q0 = cinfo.quant_tbl_ptrs[0] ? (int)cinfo.quant_tbl_ptrs[0]->quantval[0] : -1;
            int h0 = cinfo.dc_huff_tbl_ptrs[0] ? (int)cinfo.dc_huff_tbl_ptrs[0]->bits[2] : -1;
            int qt_latched = (cinfo.comp_info != NULL && cinfo.comp_info[0].quant_table != NULL) ? 1 : 0;
            printf("rh ret=%d st=%d w=%u h=%u nc=%d outcs=%d dct=%d prog=%d hms=%d eoi=%d bib=%zu ns=%d q0=%d qt=%d h0=%d warn=%ld\n",
                   ret, cinfo.global_state, cinfo.image_width, cinfo.image_height,
                   cinfo.num_components, (int)cinfo.out_color_space, (int)cinfo.dct_method,
                   cinfo.progressive_mode, cinfo.inputctl->has_multiple_scans,
                   cinfo.inputctl->eoi_reached, cinfo.src->bytes_in_buffer,
                   nsaved, q0, qt_latched, h0, jerr.pub.num_warnings);
            if (fill_mode == 1) cinfo.src = NULL;
            jpeg_destroy_decompress(&cinfo);
        } else if (strcmp(tok[0], "consume_seq") == 0 && nt == 5) {
            int init_st = (int)parse_i(tok[1]);
            int fill_mode = (int)parse_i(tok[2]);
            int steps = (int)parse_i(tok[3]);
            unsigned char buf[4096];
            unsigned char dummy[1] = {0};
            size_t nbytes = 0;
            if (!parse_hex_buf(tok[4], buf, sizeof(buf), &nbytes)) { bad = 1; continue; }
            struct jpeg_decompress_struct cinfo;
            struct err_env jerr;
            struct jpeg_source_mgr susp_src;
            memset(&cinfo, 0, sizeof(cinfo));
            cinfo.err = jpeg_std_error(&jerr.pub);
            jerr.pub.error_exit = test_error_exit;
            if (setjmp(jerr.jmp)) {
                printf("err %d %d\n", jerr.pub.msg_code, jerr.pub.msg_parm.i[0]);
                if (fill_mode == 1) cinfo.src = NULL;
                jpeg_destroy_decompress(&cinfo);
                continue;
            }
            jpeg_create_decompress(&cinfo);
            setup_src(&cinfo, fill_mode, &susp_src, buf, nbytes, dummy);
            if (init_st != 200) cinfo.global_state = init_st;
            char out[1024];
            size_t pos = 0;
            for (int s = 0; s < steps; s++) {
                int r = jpeg_consume_input(&cinfo);
                int n = snprintf(out + pos, sizeof(out) - pos, " %d:%d:%d",
                                 r, cinfo.global_state, cinfo.inputctl->eoi_reached);
                if (n > 0 && pos + (size_t)n < sizeof(out)) pos += (size_t)n;
            }
            out[pos] = '\0';
            printf("cs%s hms=%d warn=%ld\n", out, cinfo.inputctl->has_multiple_scans, jerr.pub.num_warnings);
            if (fill_mode == 1) cinfo.src = NULL;
            jpeg_destroy_decompress(&cinfo);
        } else if (strcmp(tok[0], "finish") == 0 && nt == 5) {
            int init_st = (int)parse_i(tok[1]);
            boolean eoi = (boolean)parse_i(tok[2]);
            int fill_mode = (int)parse_i(tok[3]);
            unsigned char buf[4096];
            unsigned char dummy[1] = {0};
            size_t nbytes = 0;
            if (!parse_hex_buf(tok[4], buf, sizeof(buf), &nbytes)) { bad = 1; continue; }
            struct jpeg_decompress_struct cinfo;
            struct err_env jerr;
            struct jpeg_source_mgr susp_src;
            memset(&cinfo, 0, sizeof(cinfo));
            cinfo.err = jpeg_std_error(&jerr.pub);
            jerr.pub.error_exit = test_error_exit;
            if (setjmp(jerr.jmp)) {
                printf("err %d %d\n", jerr.pub.msg_code, jerr.pub.msg_parm.i[0]);
                if (fill_mode == 1) cinfo.src = NULL;
                jpeg_destroy_decompress(&cinfo);
                continue;
            }
            jpeg_create_decompress(&cinfo);
            setup_src(&cinfo, fill_mode, &susp_src, buf, nbytes, dummy);
            cinfo.global_state = init_st;
            cinfo.inputctl->eoi_reached = eoi;
            boolean r = jpeg_finish_decompress(&cinfo);
            printf("fin ret=%d st=%d bib=%zu eoi=%d warn=%ld\n",
                   r, cinfo.global_state, cinfo.src->bytes_in_buffer,
                   cinfo.inputctl->eoi_reached, jerr.pub.num_warnings);
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
