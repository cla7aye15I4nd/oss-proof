/* Open defect (no patch). A gzwrite of at least the buffer size writes (transparent mode) or compresses straight
 * from the caller's buffer: strm.next_in points into it. When write() fails, gzwrite returns 0 with avail_in still
 * nonzero, so next_in keeps pointing into the caller's buffer after gzwrite has returned. gzclose then calls
 * gz_comp(state, Z_FINISH), which writes avail_in bytes from next_in: here the caller has freed the buffer, a read of
 * freed memory whose contents go to the file. The failure is a transient one: a non-blocking pipe that is full
 * (EAGAIN), drained before gzclose. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <fcntl.h>
#include <unistd.h>
#include "zlib.h"
int main(void) {
  int p[2];
  if (pipe(p) != 0) { printf("pipe failed\n"); return 2; }
  fcntl(p[1], F_SETFL, fcntl(p[1], F_GETFL) | O_NONBLOCK);
  fcntl(p[0], F_SETFL, fcntl(p[0], F_GETFL) | O_NONBLOCK);
  char fill[4096];
  memset(fill, 'f', sizeof fill);
  while (write(p[1], fill, sizeof fill) > 0) {}   /* the pipe is full */
  while (write(p[1], fill, 1) > 0) {}
  gzFile f = gzdopen(p[1], "wT");
  if (f == NULL) { printf("gzdopen failed\n"); return 2; }
  gzbuffer(f, 8);
  char *big = malloc(100);
  memset(big, 'a', 100);
  int r1 = gzwrite(f, big, 100);
  free(big);
  while (read(p[0], fill, sizeof fill) > 0) {}    /* drain the pipe */
  int r2 = gzclose(f);
  printf("gzclose %d %d\n", r1, r2);
  close(p[0]);
  return 0;
}
