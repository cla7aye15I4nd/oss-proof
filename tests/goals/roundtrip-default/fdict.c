/* Why Goal.uncompress_completes needs NoDictionaryRequest: a zlib stream with FDICT set and DICTID =
 * adler32 of the empty dictionary (1) satisfies Zlib.Decodes [] (the format with no dictionary), but
 * the real uncompress returns Z_DATA_ERROR on it (inflate returns Z_NEED_DICT). Exit 0 when the C
 * still behaves so. */
#include <stdio.h>
#include <string.h>
#include <zlib.h>
int main(void) {
    const unsigned char in[] = "hello hello hello";
    unsigned char c[100], d[100], s[104];
    uLongf cl = sizeof c, dl = sizeof d;
    if (compress(c, &cl, in, sizeof in - 1) != Z_OK) return 2;
    unsigned cmf = c[0], flg = 0x20;
    flg += 31 - (cmf * 256 + flg) % 31;          /* FCHECK; FDICT stays set */
    uLong id = adler32(0, Z_NULL, 0);
    s[0] = (unsigned char)cmf; s[1] = (unsigned char)flg;
    s[2] = (unsigned char)(id >> 24); s[3] = (unsigned char)(id >> 16); s[4] = (unsigned char)(id >> 8); s[5] = (unsigned char)id;
    memcpy(s + 6, c + 2, cl - 2);
    int rc = uncompress(d, &dl, s, cl + 4);
    printf("FDICT=%u DICTID=%lu uncompress rc=%d\n", (flg >> 5) & 1, id, rc);
    return rc == Z_DATA_ERROR ? 0 : 1;
}
