# inflateCopy compares pointers into different objects (patch 0001)

`inflateCopy` tests whether `state->lencode` points into the state's own code array with `>=` and
`<=`. After a fixed block it points into the static table `lenfix`, and C defines a relational
comparison only for pointers into one object. `repro.c` decodes a fixed block and calls
`inflateCopy`. `run.sh` builds the source with every patch but 0001 and the verified source, both
with the pointer-pair check of AddressSanitizer: the first must report an invalid pointer pair in
`inflateCopy`, the second nothing, with `inflateCopy` returning `Z_OK` (`report.txt`).

Run: `ZLIB_SRC=$PWD/zlib bash tests/regression/inflate-copy-fixed/run.sh`.
