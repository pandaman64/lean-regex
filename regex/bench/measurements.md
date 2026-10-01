# Benchmark history

Timings recorded while the refined PikeVM was built. Each column is one commit on `cursor/refined-flat-pikevm-40eb`. Numbers are recovered from the session log, at the precision that log recorded. Later commits that do not change the engine are listed so the table stays aligned with `git log`.

All of these runs are on this VM (4 vCPUs, KVM, no hardware performance counters). They are wall-clock averages from `lake exe Bench`. rebar's published tables are a different machine and are not repeated here. See `bench/rebar/README.md` for the curated tasks and their sources.

Match counts agreed between the stock PikeVM and the refined PikeVM in every paired run.

## Commits

| Commit | Engine change |
| --- | --- |
| `c7e8984` | Flat PikeVM, NFA words in `Array UInt32`, ε-stack in reusable arrays |
| `1f7db4e` | Same engine, words in a `ByteArray` with a wide `UInt32` load. Scratch was still filled with one `push` per byte |
| `6ecf45e` | Scratch words allocated as one zeroed block |
| `9bb0a97` | `lake exe Bench --rebar`. Same engine as `6ecf45e` |
| `f9e45db` | `--rebar-only`. Same engine as `6ecf45e`. `SW_CPU_CLOCK` profiles below were taken here |
| `bcc3ddd` | Capture slots in one unboxed `ByteArray` (`FlatBuffer`), block reused across matches |

`c7e8984` and `1f7db4e` were remeasured in one later session, refined engine only. The log does not have a stock column for that session. `6ecf45e` and `bcc3ddd` have stock and refined from the same invocation. Stock averages moved a few percent between those two sessions, so a speedup uses the stock figure from its own session.

## Synthetic haystack

One sentence repeated 67108 times, about 8.4MB (`/tmp/haystack.txt` in the session). Three iterations. The `6ecf45e` pair was two processes. The `bcc3ddd` pair was one process (`-E both`). Averages are milliseconds per iteration.

| Pattern | Matches | `c7e8984` refined | `1f7db4e` refined | `6ecf45e` stock | `6ecf45e` refined | `bcc3ddd` stock | `bcc3ddd` refined |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `def` | 201324 | 323.4 | 373.6 | 582.2 | 309.2 | 596.6 | 197.0 |
| `def\|foo\|bar` | 335540 | 689.2 | 852.6 | 1331.5 | 609.1 | 1374.2 | 430.5 |
| `\w+` | 1610592 | 1218.6 | 1685.6 | 1898.4 | 1109.0 | 1921.8 | 532.5 |
| `\d{4}-\d{2}-\d{2}` | 67108 | 481.1 | 513.0 | 952.1 | 460.4 | 957.0 | 315.1 |

Speedup of refined over the stock column of the same session:

| Pattern | `6ecf45e` | `bcc3ddd` |
| --- | ---: | ---: |
| `def` | 1.88× | 3.03× |
| `def\|foo\|bar` | 2.19× | 3.19× |
| `\w+` | 1.71× | 3.61× |
| `\d{4}-\d{2}-\d{2}` | 2.07× | 3.04× |

`c7e8984`'s commit message describes that first measurement as about 1.7× to 2.3× on this haystack. The per-case milliseconds above for `c7e8984` are the later refined-only remeasure, not that original stdout.

The `bcc3ddd` averages, before rounding, were 596.593824 / 196.993299, 1374.194976 / 430.483487, 1921.823351 / 532.473857, and 956.975412 / 315.137291 (stock / refined).

## rebar curated tasks

`lake exe Bench --rebar -n 3 -E both` from `regex/`, one process. First taken at `9bb0a97` (engine identical to `6ecf45e`). Taken again at `bcc3ddd`. Milliseconds per iteration.

| Benchmark | Matches | `9bb0a97` stock | `9bb0a97` refined | `bcc3ddd` stock | `bcc3ddd` refined |
| --- | ---: | ---: | ---: | ---: | ---: |
| `curated/literal/sherlock-en` | 513 | 74.5 | 37.5 | 77.4 | 26.7 |
| `curated/literal/sherlock-casei-en` | 522 | 110.7 | 57.4 | 116.2 | 42.5 |
| `curated/literal/sherlock-zh` | 30 | 22.1 | 11.6 | 23.4 | 8.7 |
| `curated/literal-alternate/sherlock-en` | 714 | 290.4 | 119.4 | 299.5 | 105.6 |
| `curated/words/all-english` | 15008 | 22.8 | 14.4 | 23.0 | 8.3 |
| `curated/bounded-repeat/letters-en` | 1833 | 33.0 | 17.2 | 34.1 | 13.6 |
| `curated/cloud-flare-redos/simplified-long` | 1 | 3.6 | 1.8 | 3.8 | 1.5 |

`words/all-english` and `cloud-flare-redos/simplified-long` are rebar `count-spans` tasks. The match column is the number of matches from this VM. rebar's published figure for those two is a sum of match lengths.

Throughput in the `9bb0a97` log, MB/s, from those averages and the haystack bytes (en-sampled 899232, zh-sampled 813478, words slice 76401, letters slice 151522, cloud-flare haystack 10001):

| Benchmark | `9bb0a97` stock | `9bb0a97` refined |
| --- | ---: | ---: |
| `curated/literal/sherlock-en` | 12.1 | 24.0 |
| `curated/literal/sherlock-casei-en` | 8.1 | 15.7 |
| `curated/literal/sherlock-zh` | 36.8 | 69.9 |
| `curated/literal-alternate/sherlock-en` | 3.1 | 7.5 |
| `curated/words/all-english` | 3.3 | 5.3 |
| `curated/bounded-repeat/letters-en` | 4.6 | 8.8 |
| `curated/cloud-flare-redos/simplified-long` | 2.7 | 5.6 |

The `bcc3ddd` averages, before rounding, were:

| Benchmark | Stock | Refined |
| --- | ---: | ---: |
| `curated/literal/sherlock-en` | 77.426219 | 26.669975 |
| `curated/literal/sherlock-casei-en` | 116.235564 | 42.531788 |
| `curated/literal/sherlock-zh` | 23.448576 | 8.662698 |
| `curated/literal-alternate/sherlock-en` | 299.452584 | 105.592932 |
| `curated/words/all-english` | 22.993909 | 8.265189 |
| `curated/bounded-repeat/letters-en` | 34.095021 | 13.563892 |
| `curated/cloud-flare-redos/simplified-long` | 3.775831 | 1.459676 |

## `SW_CPU_CLOCK` profiles

User-space samples, period 200 µs, every thread of the Bench process. Sampled CPU milliseconds are `samples × 0.2`. Lost samples were 0. Iteration counts were chosen so the stock engine had about 2–3 s of sampled CPU. The same `-n` was used for both engines.

`f9e45db` (same engine as `6ecf45e`). Interpreter time is `εClosure` + `Regex.findAll.go` + sparse-set clearing for stock, and `Refined.findAll.go` for refined. Alloc/RC is mimalloc, reference counting, and array copy/free.

| Benchmark | `-n` | Stock CPU | Refined CPU | Stock interpreter | Refined interpreter | Stock alloc/RC | Refined alloc/RC |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `curated/literal/sherlock-en` | 40 | 3089 | 1544 | 1354 | 987 | 1540 | 415 |
| `curated/literal/sherlock-casei-en` | 25 | 2875 | 1495 | 1240 | 865 | 1266 | 279 |
| `curated/literal/sherlock-zh` | 100 | 2341 | 1204 | 962 | 783 | 1144 | 237 |
| `curated/literal-alternate/sherlock-en` | 10 | 3049 | 1209 | 1409 | 1032 | 1500 | 131 |
| `curated/words/all-english` | 100 | 2351 | 1477 | 808 | 577 | 1132 | 589 |
| `curated/bounded-repeat/letters-en` | 70 | 2435 | 1272 | 1019 | 685 | 1034 | 191 |
| `curated/cloud-flare-redos/simplified-long` | 600 | 2336 | 1106 | 1032 | 827 | 1075 | 123 |

Sample counts in that run: stock / refined = 15446 / 7720, 14377 / 7476, 11705 / 6021, 15247 / 6045, 11754 / 7383, 12176 / 6362, 11678 / 5530.

`bcc3ddd`, refined only, same `-n` and the same sampler. casei, zh, and the cloud-flare pattern were not profiled again.

| Benchmark | `-n` | Refined CPU | Refined alloc/RC | Samples |
| --- | ---: | ---: | ---: | ---: |
| `curated/literal/sherlock-en` | 40 | 1045 | 6 | 5223 |
| `curated/literal-alternate/sherlock-en` | 10 | 1051 | 12 | 5254 |
| `curated/words/all-english` | 100 | 846 | 129 | 4228 |
| `curated/bounded-repeat/letters-en` | 70 | 990 | 17 | 4951 |

## Compiled class tables

`Classes` is still the tree. `ofNFA` compiles each tree into runs once: complement, intersection, difference, and symmetric difference are set algebra on those runs, and a perl class is the ASCII ranges for digit, space, or word. The match loop does not branch on the operator.

The kept table is a Latin-1 bitmap for `c < 256` and a linear scan of the runs clipped to `≥ 256`. An empty high list means the character is not in the set. Bitmap-only, full-run linear, full-run binary, and bitmap-plus-binary were measured on a fatter struct and then removed. The bitmap was the ASCII win. A linear or binary scan of one to four runs did not beat the tree on the two-code-point case-insensitive classes, and binary did not beat linear at those run counts. Bitmap-only was slower than the tree on the zh letter class, because every non-ASCII character fell back to `Classes.mem`.

Same session after that removal, refined engine, milliseconds per iteration. `tree` is `b42f6f6`. `ef3489f` is the slim bitmap-plus-linear binary. Match counts agreed on every row (1833, 522, 15008, 1, 513, 668, 9913). `sherlock-en` has no character class; it moved anyway, so a gap versus `tree` is not only the class probe.

| Benchmark | `-n` | `b42f6f6` tree | `ef3489f` bitmap+linear |
| --- | ---: | ---: | ---: |
| `letters-en` `[A-Za-z]` | 40 | 13.766 | 10.327 |
| `sherlock-casei-en` | 20 | 42.775 | 32.395 |
| `words/all-english` `\w` | 50 | 8.248 | 6.766 |
| `simplified-long` `.` | 300 | 1.495 | 1.173 |
| `sherlock-en` literal | 20 | 26.687 | 23.073 |
| `[A-Za-z]{8,13}` on zh-sampled | 20 | 15.529 | 12.306 |
| `\w+` on zh-sampled | 20 | 13.099 | 11.624 |

Same binary, stock PikeVM and refined in one process (`-E both`, stock first). Milliseconds per iteration. Match counts agreed.

| Benchmark | `-n` | Stock | Refined | Speedup |
| --- | ---: | ---: | ---: | ---: |
| `letters-en` `[A-Za-z]` | 40 | 33.985 | 10.238 | 3.32× |
| `sherlock-casei-en` | 20 | 118.335 | 32.358 | 3.66× |
| `words/all-english` `\w` | 50 | 23.209 | 6.650 | 3.49× |
| `simplified-long` `.` | 300 | 3.917 | 1.187 | 3.30× |
| `sherlock-en` literal | 20 | 78.937 | 23.024 | 3.43× |
| `sherlock-zh` literal | 20 | 23.479 | 7.595 | 3.09× |
| `literal-alternate/sherlock-en` | 10 | 308.398 | 93.068 | 3.31× |
| `[A-Za-z]{8,13}` on zh-sampled | 20 | 40.975 | 12.313 | 3.33× |
| `\w+` on zh-sampled | 20 | 41.214 | 11.721 | 3.52× |

## `SW_CPU_CLOCK` after the class table

Refined only, period 200 µs, lost samples 0, four threads. Each run is about 2.2 s of sampled CPU. `Classes.mem` took no samples. The probe is inlined into `Refined.search`: a Latin-1 `bt` on the bitmap, and a linear scan of the high runs only when the code point is at least 256.

Shares are of all samples. The bitmap column is that `bt` block. The linear column is the high-run loop. Before this table, on the tree walk, `Classes.mem` was 32.8% of `letters-en`, 22.9% of `sherlock-casei-en`, 16.3% of `words/all-english`, and 14.4% of `simplified-long`.

| Benchmark | `-n` | Samples | `search` | Bitmap | Linear high |
| --- | ---: | ---: | ---: | ---: | ---: |
| `letters-en` `[A-Za-z]` | 220 | 11885 | 98.1% | 10.0% | 0.0% |
| `sherlock-casei-en` | 70 | 11550 | 98.9% | 7.3% | 0.0% |
| `words/all-english` `\w` | 330 | 11405 | 61.2% | 1.9% | 0.0% |
| `simplified-long` `.` | 1850 | 11224 | 98.8% | 3.6% | 0.0% |
| `sherlock-en` literal | 95 | 12125 | 98.6% | 0.0% | 0.0% |
| `[A-Za-z]{8,13}` on zh-sampled | 180 | 11430 | 95.0% | 4.7% | 1.7% |
| `\w+` on zh-sampled | 190 | 11827 | 92.3% | 2.9% | 0.7% |

On the ASCII class benches the bitmap is one block among several inside `search`. On `letters-en` it is the hottest block, at 10%. The next blocks are the sparse-set probe (9.0%), the loop reload that increments a reference count and restores the live set (8.1%), and the node load of tag, next, and extra (6.5%). On `sherlock-casei-en` the node load is ahead of the bitmap, 12.3% against 7.3%.

`words/all-english` leaves `search` for the word-boundary helpers: `mi_malloc_small` 8.0%, `String.Pos.Raw.isValidForSlice` 7.6%, `String.isPrevWord` 6.3%, `mi_free` 3.8%, `Anchor.test` 3.2%. The Chinese haystacks add the UTF-8 cold path: `lean_string_utf8_get_fast_cold` 2.7% and `lean_string_utf8_next_fast_cold` 1.0% on `[A-Za-z]{8,13}`, and 2.7% / 1.2% on `\w+`. The `lean_copy_byte_array` call instructions themselves were not sampled.

## Word boundaries

`words/all-english` is `\b[0-9A-Za-z_]+\b`. After the class table, `search` was about 61% of that bench. The rest was `String.Pos.prev`: it allocates a `Slice` and walks backward through `isValidForSlice`. Three changes, each benched and profiled against the previous binary. `Anchor.test` and `Char.isWordChar` stay the specification. The refined loop uses `anchorTest`. `bench --check` agreed with the stock VM, including `café`, `漢字`, and `\B`. Match counts agreed on every timing run: words 15008, `letters-en` 1833, `\b\w+\b` on zh-sampled 9913.

| Commit | Change |
| --- | --- |
| `23eaf00` | `String.Pos.Raw.prev` (`lean_string_utf8_prev`) instead of `String.Pos.prev`. Classification is still `Char.isWordChar` |
| `4929469` | Classify with `wordTable`, the Latin-1 bitmap plus high runs of a perl word class. Today that set is ASCII. A Unicode `\w` fills the high runs; the boundary stays `mem(curr) ≠ mem(prev)` |
| `3b12a5f` | Carry three `UInt64`s through every `eval` tail call: the byte offset just classified, the next scalar's offset, and three bits (previous word, current word, ready). The same offset reuses the bits. The next scalar reuses the old current bit as its previous bit, so `utf8_prev` runs only on a cold offset. Each `findAll` search starts the latch clear, so the first boundary of a match is still cold |

Same-session pairs, refined engine only, milliseconds per iteration. `letters-en` has no `\b`. It moves a few percent across rebuilds; the larger gap on the latch is the extra parameters.

| Benchmark | `-n` | base (`5c68581`) | `23eaf00` `utf8_prev` |
| --- | ---: | ---: | ---: |
| `words/all-english` | 100 | 6.701 | 6.195 |
| `letters-en` | 40 | 10.616 | 10.160 |
| `\b\w+\b` on zh-sampled | 30 | 18.095 | 14.737 |

| Benchmark | `-n` | `23eaf00` | `4929469` table | `3b12a5f` scalar latch |
| --- | ---: | ---: | ---: | ---: |
| `words/all-english` | 100 | 6.210 | 6.507 | 6.418 |
| `letters-en` | 40 | 10.183 | 10.646 | 11.435 |
| `\b\w+\b` on zh-sampled | 30 | 14.692 | 16.540 | 14.957 |

The first step is the speed change. The `Slice` allocation and the Lean backward scan leave the profile, and the Chinese haystack drops from 18.1 ms to 14.7 ms. The class table is slower than `Char.isWordChar` (words 6.21 → 6.51, zh 14.7 → 16.5) because a table probe after a full decode does not beat a few ASCII compares. It is the representation a Unicode property can fill. The scalar latch takes `utf8_prev` off the hot samples and brings zh back to 15.0 ms, near the first step, but it does not beat that step on English words (6.42 against 6.21). `letters-en` goes from about 10.2 ms to 11.4 ms with the profile still inside `search`.

A `WordLatch` structure was measured in between and not kept. Constructing it on a position change allocated. Same session as the table binary it was built from, milliseconds per iteration: words 6.515 → 7.541, letters 10.633 → 11.103, zh 16.482 → 17.183.

### Profiles

Refined only, period 200 µs, lost samples 0, four threads. Shares are of all samples.

`words/all-english`:

| Step | `-n` | Samples | `search` | Outside `search` |
| --- | ---: | ---: | ---: | --- |
| base | 330 | 11392 | 62.6% | `mi_malloc_small` 7.6%, `isValidForSlice` 7.5%, `isPrevWord` 6.2%, `mi_free` 3.5%, `Anchor.test` 3.1%, `IsUTF8FirstByte` 2.1% |
| `23eaf00` | 330 | 10608 | 85.7% | `mi_free` 2.7%, `mi_malloc_small` 2.2%, `utf8_prev` 2.1%, `utf8_get` 1.8%. `isPrevWord`, `isValidForSlice`, and `Anchor.test` took no samples |
| `4929469` | 330 | 11156 | 84.8% | `utf8_get` 3.6%, `mi_malloc_small` 2.4%, `utf8_prev` 1.8%, `mi_free` 1.6% |
| `3b12a5f` | 340 | 11135 | 88.2% | `mi_malloc_small` 2.3%, `mi_free` 2.3%, `utf8_get` 1.4%. `utf8_prev` 0.2% |

`\b\w+\b` on zh-sampled:

| Step | `-n` | Samples | `search` | Outside `search` |
| --- | ---: | ---: | ---: | --- |
| base | 120 | 11202 | 54.2% | `isValidForSlice` 11.6%, `isPrevWord` 6.9%, `mi_malloc_small` 6.8%, `Anchor.test` 4.4%, `IsUTF8FirstByte` 3.6%, `utf8_get_fast_cold` 3.0% |
| `23eaf00` | 150 | 11104 | 83.0% | `utf8_prev` 4.5%, `utf8_get_core` 3.5%, `utf8_get` 2.4%, `utf8_get_fast_cold` 2.4% |
| `4929469` | 130 | 10990 | 81.0% | `utf8_get_core` 6.5%, `utf8_get` 4.5%, `utf8_prev` 4.1% |
| `3b12a5f` | 150 | 11405 | 87.0% | `utf8_get_core` 4.9%, `utf8_get` 2.5%, `utf8_next_fast_cold` 1.9%. `utf8_prev` 0.1% |

`letters-en` on `3b12a5f`, `-n` 190, 11040 samples: `search` 98.3%. No other symbol reached 0.3%. The slowdown is the extra words on the tail call, not a new helper.

The discarded structure, on words, was `search` 79.7%, `mi_malloc_small` 6.4%, `mi_free` 5.8% (11141 samples). On zh it was `search` 75.6%, `mi_malloc_small` 6.9%, `mi_free` 6.8% (10683 samples). `utf8_prev` was already 0.2% / 0.1% there; the allocation was the cost.

The tip keeps `23eaf00` only. `4929469` and `3b12a5f` were slower on these benches, so both were reverted. Classification stays `Char.isWordChar`. The class table and the scalar latch remain in the history above.

## `SW_CPU_CLOCK` inside `search` after `utf8_prev`

Refined only, on `2adb885`, period 200 µs, lost samples 0, four threads. `Refined.search` contains the inlined `eval` loop. Shares in the second table are of the samples inside that symbol. `lean_copy_byte_array` call instructions took no samples. The `call` instructions for `utf8_prev` and `utf8_get` took none either; those samples sit in the callees, outside `search`.

| Benchmark | `-n` | ms/iter | Samples | `search` |
| --- | ---: | ---: | ---: | ---: |
| `letters-en` `[A-Za-z]` | 220 | 10.475 | 11657 | 98.1% |
| `sherlock-casei-en` | 70 | 33.714 | 11927 | 98.8% |
| `words/all-english` | 360 | 6.872 | 12474 | 86.2% |
| `simplified-long` `.` | 1850 | 1.264 | 11795 | 98.9% |
| `sherlock-en` literal | 95 | 22.821 | 10953 | 98.6% |
| `[A-Za-z]{8,13}` on zh-sampled | 180 | 12.248 | 11131 | 95.0% |
| `\w+` on zh-sampled | 190 | 11.762 | 11289 | 91.3% |

| Part of `search` | letters | casei | words | redos | literal | letters-zh | word-zh |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Tail reload (refcount inc, restore the live set) | 10.7% | 11.1% | 11.0% | 11.5% | 11.8% | 10.4% | 11.2% |
| Sparse-set probe (`nSpa[state]`, `si < nCount`) | 6.2% | 5.7% | 9.9% | 10.4% | 14.1% | 8.1% | 11.2% |
| Probe hit (`nDen[si] == state`, then the same reload) | 4.4% | 0.6% | 1.3% | 2.2% | 0.0% | 1.5% | 0.0% |
| Closure miss: capture-row `imul`, load tag/next/extra | 6.8% | 11.7% | 9.4% | 10.4% | 12.1% | 11.1% | 11.0% |
| Step: `cDen[i]`, times 12, load tag | 4.7% | 6.0% | 6.2% | 6.2% | 5.5% | 4.7% | 6.2% |
| Enter `phaseStep` and reload | 5.2% | 6.8% | 4.4% | 3.3% | 6.8% | 6.4% | 6.2% |
| Refcount decrement | 5.6% | 5.7% | 4.0% | 3.9% | 3.9% | 5.0% | 4.1% |
| Latin-1 bitmap `bt` | 10.8% | 7.8% | 2.4% | 4.0% | 0.0% | 4.9% | 2.9% |
| Class-table pointer and the haystack byte | 5.5% | 4.1% | 1.7% | 1.4% | 0.0% | 5.6% | 2.7% |
| Inlined `Char.isWordChar` | 0.0% | 0.0% | 2.7% | 0.0% | 0.0% | 0.0% | 0.0% |

Nothing inside the loop is a majority. The three blocks that lead on every bench except the pure ASCII class are the tail reload, the sparse-set probe, and the closure-miss node load. Each is about 10–14% of `search`. The hottest instruction on `words/all-english` is the probe's `cmp` of `si` with `nCount`, 5.0% of `search`. On `sherlock-en` that same `cmp` is 7.6%. On `letters-en` the hottest instruction is the bitmap `bt`, 8.0% of `search`, and that block is still the largest there at 10.8%. On `sherlock-casei-en` the closure-miss node load leads the bitmap, 11.7% against 7.8%.

`words/all-english` is 86.2% `search`. Outside it: `mi_malloc_small` 2.3%, `utf8_prev` 2.1%, `mi_free` 1.9%, `utf8_get` 1.9%. The inlined ASCII word test is 2.7% of `search` (2.4% of all samples). The Chinese haystacks still pay the UTF-8 cold path outside `search`: `utf8_get_fast_cold` 2.7% and `utf8_next_fast_cold` 1.0% on `[A-Za-z]{8,13}`, and 3.5% / 1.1% on `\w+`.

## Reversed flat nodes

`771c078` stores the flat buffer last node first and rewrites state ids, so a transition that compilation pointed at an earlier node now points forward. `done` and `fail` keep a zero successor. A split's second successor moves with the nodes. Save slots and class-table indexes do not. The match loop source is unchanged. The two `search` functions are the same 2140 instructions once branch targets are ignored. `bench --check` agreed with the stock VM. Match counts agreed.

Refined only, milliseconds per iteration. The forward binary is the engine before this commit.

| Benchmark | `-n` | Forward | `771c078` reversed |
| --- | ---: | ---: | ---: |
| `letters-en` `[A-Za-z]` | 100 | 10.264 | 11.260 |
| `sherlock-casei-en` | 40 | 33.120 | 35.282 |
| `words/all-english` | 150 | 6.193 | 6.565 |
| `simplified-long` `.` | 800 | 1.262 | 1.310 |
| `sherlock-en` literal | 50 | 22.150 | 24.155 |
| `[A-Za-z]{8,13}` on zh-sampled | 80 | 12.089 | 12.877 |
| `\w+` on zh-sampled | 80 | 11.729 | 12.382 |

Every row is slower, from 3.8% on `simplified-long` to 9.7% on `letters-en`. The literal, whose NFA is a handful of nodes, moved with the rest, so the gap is not only a long backward chain.

The tip drops `771c078`. `ofNFA` stores nodes in compilation order again.

## Stock versus refined after `utf8_prev`

`8d2c203`. Both engines in one process (`-E both`, stock first). Milliseconds per iteration. Match counts agreed on every row. The earlier paired run, before `utf8_prev`, is the "Stock versus bitmap+linear" table above.

| Benchmark | `-n` | Stock | Refined | Speedup |
| --- | ---: | ---: | ---: | ---: |
| `letters-en` `[A-Za-z]` | 40 | 34.146 | 10.140 | 3.37× |
| `sherlock-casei-en` | 20 | 116.249 | 32.350 | 3.59× |
| `words/all-english` `\b…\b` | 50 | 23.317 | 6.155 | 3.79× |
| `simplified-long` `.` | 300 | 3.888 | 1.249 | 3.11× |
| `sherlock-en` literal | 20 | 78.632 | 21.922 | 3.59× |
| `sherlock-zh` literal | 20 | 23.618 | 7.473 | 3.16× |
| `literal-alternate/sherlock-en` | 10 | 306.175 | 101.813 | 3.01× |
| `[A-Za-z]{8,13}` on zh-sampled | 20 | 40.901 | 12.033 | 3.40× |
| `\w+` on zh-sampled | 20 | 41.210 | 11.759 | 3.50× |

`words/all-english` is the row that moved. In the earlier pair it was 23.209 / 6.650 (3.49×). The refined time is the `utf8_prev` walk. The other rows stay near 3.0× to 3.6×.
