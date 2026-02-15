#include "all.h"

#include <unistd.h>

uint32_t _qbe_prof_edge_counts[PROF_NEDGE];

void _qbe_prof_edge(const int edge_hash) {
    _qbe_prof_edge_counts[edge_hash]++;
}

void _qbe_prof_end(void) {
    const char* out_name = "prof.out";

    if (access(out_name, F_OK) == 0) {
        fprintf(stderr, "qbe profiler: file %s exists, refusing to overwrite!\n", out_name);
        return;
    }

    FILE* f = fopen(out_name, "w");
    if (f == NULL) {
        fprintf(stderr, "qbe profiler: could not open %s\n", out_name);
        return;
    }

    const size_t written = fwrite(_qbe_prof_edge_counts, sizeof(_qbe_prof_edge_counts[0]), PROF_NEDGE, f);
    if (written != PROF_NEDGE) {
        fprintf(stderr, "qbe profiler: warning: incomplete write to prof.out");
    }
}
