/*
 * Little-endian ByteArray word load and store for the refined PikeVM.
 *
 * Adapted, with attribution, from lean-zip's wide ByteArray primitives
 * (the `ugetUInt32LE` / `usetUInt32LE` pair and their C implementations):
 *   https://github.com/kim-em/lean-zip/blob/2f7a63f38195bc667a926881b55d10c9f8a88eeb/Zip/Native/Wide.lean
 *   https://github.com/kim-em/lean-zip/blob/2f7a63f38195bc667a926881b55d10c9f8a88eeb/c/bytearray_wide_ffi.c
 *
 * `lean_regex_uget_u32le(a, off)` reads the 4-byte little-endian word at byte
 * offset `off`, returning an unboxed `uint32_t`. The Lean reference body is
 *
 *   a[off] ||| a[off+1] <<< 8 ||| a[off+2] <<< 16 ||| a[off+3] <<< 24
 *
 * The bytes are combined explicitly so the result is little-endian on every
 * host and free of unaligned-access undefined behavior. At -O2 the compiler
 * folds the four byte loads into one wide load. The Lean side carries
 * `off + 4 ≤ a.size`, so this function does not check the bound. `a` is
 * borrowed and `off` is an unboxed `size_t`.
 *
 * `lean_regex_uset_u32le` is the matching store. This toolchain is Lean
 * v4.34.0-rc1, which still provides `lean_copy_byte_array` (the helper
 * `lean_sarray_ensure_exclusive` used by later lean-zip revisions is not in
 * this runtime). The exclusive / copy split therefore follows
 * `lean_byte_array_uset` in this header: mutate in place when `a` is
 * exclusive, otherwise copy first.
 *
 * Symbols are namespaced `lean_regex_*` so they do not clash with lean-zip
 * or with a future core `uget*` primitive (lean#14053).
 */

#include <lean/lean.h>
#include <stdint.h>

LEAN_EXPORT uint32_t lean_regex_uget_u32le(b_lean_obj_arg a, size_t off) {
    const uint8_t *p = lean_sarray_cptr(a) + off;
    return (uint32_t)p[0]
        | ((uint32_t)p[1] << 8)
        | ((uint32_t)p[2] << 16)
        | ((uint32_t)p[3] << 24);
}

LEAN_EXPORT lean_obj_res lean_regex_uset_u32le(lean_obj_arg a, size_t off, uint32_t v) {
    lean_obj_res r;
    if (lean_is_exclusive(a)) r = a;
    else r = lean_copy_byte_array(a);
    uint8_t *p = lean_sarray_cptr(r) + off;
    p[0] = (uint8_t)v;
    p[1] = (uint8_t)(v >> 8);
    p[2] = (uint8_t)(v >> 16);
    p[3] = (uint8_t)(v >> 24);
    return r;
}

/*
 * `n` zero bytes in one scalar array. `lean_alloc_sarray` does not clear the
 * payload, so the bytes are memset here. Scratch buffers are rebuilt for every
 * match; filling them with `ByteArray.push` made that setup dominate `\w+`.
 */
LEAN_EXPORT lean_obj_res lean_regex_zero_byte_array(size_t n) {
    lean_obj_res a = lean_alloc_sarray(1, n, n);
    uint8_t *p = lean_sarray_cptr(a);
    for (size_t i = 0; i < n; i++) p[i] = 0;
    return a;
}
