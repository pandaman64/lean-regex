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

## Lean `ugetUInt32LE!` (not kept)

Tried a safe bounds check in Lean in front of the existing wide load. `ugetUInt32LE!` / `usetUInt32LE!` tested `off.toNat + 4 ≤ a.size`. The in-range arm called `lean_regex_uget_u32le` / `lean_regex_uset_u32le`. Out of range, a load returned `0` and a store returned the array unchanged. `WordArray.uget` / `uset` used that path, so NFA word traffic no longer passed `lcProof`.

`--check` passed, and every paired run below found the same match count as the unchecked engine. After LTO the scalar arm is not a call to `lean_nat_add`: it unboxes, adds 4, compares the tagged sizes, and then does the wide `movl`. The heap-`Nat` helpers sit on the overflow arm. That still adds several arithmetic instructions to every word load and store. The refined loop loads three words per state, so the extra work shows up.

Same session, two binaries, refined engine only. Unchecked is `b42f6f6`. The `!` column is the build that wired `WordArray` to the Lean check. Milliseconds per iteration.

| Benchmark | `-n` | Unchecked | `uget!` | Change |
| --- | ---: | ---: | ---: | ---: |
| `curated/literal/sherlock-en` | 3 | 26.876081 | 28.478139 | +6.0% |
| `curated/literal/sherlock-casei-en` | 3 | 42.707268 | 50.287682 | +17.7% |
| `curated/literal-alternate/sherlock-en` | 3 | 105.803729 | 134.052459 | +26.7% |
| `curated/literal-alternate/sherlock-en` | 5 | 105.242534 | 142.608889 | +35.5% |
| `curated/words/all-english` | 20 | 8.282900 | 9.652657 | +16.5% |
| `curated/bounded-repeat/letters-en` | 3 | 13.810801 | 16.338624 | +18.3% |
| synthetic `def` | 3 | 199.054414 | 208.670633 | +4.8% |
| synthetic `\w+` | 3 | 546.241397 | 638.373057 | +16.9% |

`words` at `-n 3` was too short to trust (the first pair flipped direction). At `-n 20` it matches the other word-heavy benches. The check was not left on the hot path. `WordArray.uget` / `uset` again call the unchecked extern with `lcProof`.
