# rebar curated benchmarks

These search tasks are taken from the curated set in
[BurntSushi/rebar](https://github.com/BurntSushi/rebar), a barometer for the
relative speed of regex engines. The patterns, haystacks, and line slices below
are that repository's definitions. They are not results copied from rebar.

Run them from the `regex` package directory:

```
lake exe Bench --rebar -n 3 -E both
```

`--rebar-dir` overrides the haystack directory. The default is
`bench/rebar/haystacks`.

| Benchmark | Original definition |
| --- | --- |
| `curated/literal/sherlock-en` | [01-literal.toml](https://github.com/BurntSushi/rebar/blob/master/benchmarks/definitions/curated/01-literal.toml) |
| `curated/literal/sherlock-casei-en` | [01-literal.toml](https://github.com/BurntSushi/rebar/blob/master/benchmarks/definitions/curated/01-literal.toml) |
| `curated/literal/sherlock-zh` | [01-literal.toml](https://github.com/BurntSushi/rebar/blob/master/benchmarks/definitions/curated/01-literal.toml) |
| `curated/literal-alternate/sherlock-en` | [02-literal-alternate.toml](https://github.com/BurntSushi/rebar/blob/master/benchmarks/definitions/curated/02-literal-alternate.toml) |
| `curated/words/all-english` | [08-words.toml](https://github.com/BurntSushi/rebar/blob/master/benchmarks/definitions/curated/08-words.toml) |
| `curated/bounded-repeat/letters-en` | [10-bounded-repeat.toml](https://github.com/BurntSushi/rebar/blob/master/benchmarks/definitions/curated/10-bounded-repeat.toml) |
| `curated/cloud-flare-redos/simplified-long` | [06-cloud-flare-redos.toml](https://github.com/BurntSushi/rebar/blob/master/benchmarks/definitions/curated/06-cloud-flare-redos.toml) |

`sherlock-casei-en` is rebar's case-insensitive flag, written here as the
inline flag `(?i)` that this parser accepts. `words/all-english` keeps rebar's
`line-end = 2500` slice (lines are 0-indexed and `line-end` is exclusive).
`bounded-repeat/letters-en` keeps `line-end = 5000`.

Where rebar's model is `count`, the runner checks its published match count.
`words/all-english` and `cloud-flare-redos/simplified-long` use rebar's
`count-spans` model (a sum of match lengths), so the runner only checks that
the two engines agree on the number of matches.

Haystacks, copied from rebar so the option can re-run without fetching:

- `opensubtitles/en-sampled.txt` and `opensubtitles/zh-sampled.txt` are rebar's
  files of the same name
  ([en](https://github.com/BurntSushi/rebar/blob/master/benchmarks/haystacks/opensubtitles/en-sampled.txt),
  [zh](https://github.com/BurntSushi/rebar/blob/master/benchmarks/haystacks/opensubtitles/zh-sampled.txt)).
  rebar derived them from the OpenSubtitles corpus:
  <https://opus.nlpl.eu/OpenSubtitles-v2018.php>
- `cloud-flare-redos.txt` is rebar's
  [cloud-flare-redos.txt](https://github.com/BurntSushi/rebar/blob/master/benchmarks/haystacks/cloud-flare-redos.txt).
