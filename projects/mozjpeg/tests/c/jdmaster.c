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
        char *tok[16];
        int nt = split(line, tok, 16);
        if (nt == 0) continue;
        if ((strcmp(tok[0], "core") == 0 || strcmp(tok[0], "calc") == 0) && nt == 15) {
            int is_calc = (strcmp(tok[0], "calc") == 0);
            int gstate = (int)parse_i(tok[1]);
            int lossless = (int)parse_i(tok[2]);
            unsigned int w = (unsigned int)parse_u(tok[3]);
            unsigned int h = (unsigned int)parse_u(tok[4]);
            unsigned int snum = (unsigned int)parse_u(tok[5]);
            unsigned int sden = (unsigned int)parse_u(tok[6]);
            int nc = (int)parse_i(tok[7]);
            int jpeg_cs = (int)parse_i(tok[8]);
            int out_cs = (int)parse_i(tok[9]);
            int fancy = (int)parse_i(tok[10]);
            int ccir = (int)parse_i(tok[11]);
            int quant = (int)parse_i(tok[12]);
            int maxh = (int)parse_i(tok[13]);
            int maxv = (int)parse_i(tok[14]);

            struct jpeg_decompress_struct cinfo;
            struct err_env jerr;
            memset(&cinfo, 0, sizeof(cinfo));
            cinfo.err = jpeg_std_error(&jerr.pub);
            jerr.pub.error_exit = test_error_exit;

            unsigned char *master_buf = (unsigned char *)calloc(1, 512);
            struct jpeg_decomp_master *mst = (struct jpeg_decomp_master *)master_buf;
            mst->lossless = lossless;

            jpeg_component_info *comps = (jpeg_component_info *)calloc(nc > 0 ? (size_t)nc : 1, sizeof(jpeg_component_info));
            if (nc >= 1) { comps[0].h_samp_factor = maxh; comps[0].v_samp_factor = maxv; }
            for (int i = 1; i < nc; i++) {
                comps[i].h_samp_factor = 1;
                comps[i].v_samp_factor = 1;
            }

            cinfo.global_state = gstate;
            cinfo.master = mst;
            cinfo.comp_info = comps;
            cinfo.image_width = w;
            cinfo.image_height = h;
            cinfo.scale_num = snum;
            cinfo.scale_denom = sden;
            cinfo.num_components = nc;
            cinfo.jpeg_color_space = (J_COLOR_SPACE)jpeg_cs;
            cinfo.out_color_space = (J_COLOR_SPACE)out_cs;
            cinfo.do_fancy_upsampling = fancy;
            cinfo.CCIR601_sampling = ccir;
            cinfo.quantize_colors = quant;
            cinfo.max_h_samp_factor = maxh;
            cinfo.max_v_samp_factor = maxv;

            if (setjmp(jerr.jmp)) {
                printf("err %d %d\n", jerr.pub.msg_code, jerr.pub.msg_parm.i[0]);
                free(comps);
                free(master_buf);
                continue;
            }

            if (is_calc)
                jpeg_calc_output_dimensions(&cinfo);
            else
                jpeg_core_output_dimensions(&cinfo);

            printf("ok %u %u %d %d %d %d",
                   cinfo.output_width,
                   cinfo.output_height,
                   cinfo.out_color_components,
                   cinfo.output_components,
                   cinfo.rec_outbuf_height,
                   cinfo.min_DCT_h_scaled_size);
            for (int i = 0; i < nc; i++) {
                printf(" [%d,%d,%u,%u]",
                       comps[i].DCT_h_scaled_size,
                       comps[i].DCT_v_scaled_size,
                       comps[i].downsampled_width,
                       comps[i].downsampled_height);
            }
            printf("\n");
            free(comps);
            free(master_buf);
        } else {
            fprintf(stderr, "unknown command: %s\n", tok[0]);
            printf("BADINPUT\n");
            bad = 1;
        }
    }
    free(line);
    return bad;
}
