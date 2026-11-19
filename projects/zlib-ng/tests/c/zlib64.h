/* Include after zlib.h. zlib.h declares the *64 functions only where the C library defines
 * _LFS64_LARGEFILE (glibc does); elsewhere (for example on macOS, where off_t has 64 bits anyway) the
 * library still exports them, so declare them here. */
#ifndef DIFFTEST_ZLIB64_H
#define DIFFTEST_ZLIB64_H
#ifndef Z_LARGE64
unsigned long adler32_combine64(unsigned long, unsigned long, z_off64_t);
unsigned long crc32_combine64(unsigned long, unsigned long, z_off64_t);
unsigned long crc32_combine_gen64(z_off64_t);
#endif
#endif
