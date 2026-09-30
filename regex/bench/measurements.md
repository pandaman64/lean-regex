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
