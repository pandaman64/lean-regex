#include <lean/lean.h>
#include <stdint.h>
#include <string.h>

/*
 * `REGEX_BENCH_INIT` is the generated module initializer
 * (`initialize_…BenchFFI`), passed by build.rs.
 */
extern lean_object *REGEX_BENCH_INIT(uint8_t builtin);
extern uint32_t regex_bench_init(b_lean_obj_arg dir);
extern uint32_t regex_bench_n_cases(uint32_t token);
extern uint64_t regex_bench_count(uint32_t case_id, uint32_t engine);
extern lean_obj_res regex_bench_case_name(uint32_t case_id);

static int started = 0;

int regex_bench_startup(const char *dir) {
    if (!started) {
        lean_object *res = REGEX_BENCH_INIT(1);
        if (lean_io_result_is_error(res)) {
            lean_io_result_show_error(res);
            lean_dec(res);
            return 2;
        }
        lean_dec(res);
        lean_io_mark_end_initialization();
        started = 1;
    }
    lean_object *s = lean_mk_string(dir);
    uint32_t rc = regex_bench_init(s);
    lean_dec(s);
    return (int)rc;
}

uint32_t regex_bench_cases(void) {
    return regex_bench_n_cases(0);
}

uint64_t regex_bench_matches(uint32_t case_id, uint32_t engine) {
    return regex_bench_count(case_id, engine);
}

const char *regex_bench_name(uint32_t case_id) {
    static char buf[512];
    lean_object *s = regex_bench_case_name(case_id);
    char const *cstr = lean_string_cstr(s);
    strncpy(buf, cstr, sizeof(buf) - 1);
    buf[sizeof(buf) - 1] = '\0';
    lean_dec(s);
    return buf;
}
