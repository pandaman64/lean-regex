use lean_regex_bench::{count, startup, BOUNDED_RECURSOR, PIKEVM, REFINED_PIKEVM};
use std::fmt;

/// A curated case. `id` is the index in `RegexVibe.BenchFFI.cases`.
#[derive(Clone, Copy)]
struct Case {
    name: &'static str,
    id: u32,
}

impl fmt::Debug for Case {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name)
    }
}

impl fmt::Display for Case {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name)
    }
}

const CASES: &[Case] = &[
    Case {
        name: "curated/literal/sherlock-en",
        id: 0,
    },
    Case {
        name: "curated/literal/sherlock-casei-en",
        id: 1,
    },
    Case {
        name: "curated/literal/sherlock-zh",
        id: 2,
    },
    Case {
        name: "curated/literal-alternate/sherlock-en",
        id: 3,
    },
    Case {
        name: "curated/words/all-english",
        id: 4,
    },
    Case {
        name: "curated/bounded-repeat/letters-en",
        id: 5,
    },
    Case {
        name: "curated/cloud-flare-redos/simplified-long",
        id: 6,
    },
];

/// The stock PikeVM segfaults under CodSpeed's simulator on `.*.*=.*`.
/// The other two engines still time that case.
const PIKEVM_CASES: &[Case] = &[
    CASES[0], CASES[1], CASES[2], CASES[3], CASES[4], CASES[5],
];

fn main() {
    // Loading haystacks and compiling patterns is not part of a match count.
    // The first bench would otherwise include it.
    startup();
    divan::main();
}

mod regex {
    use super::*;

    #[divan::bench(args = PIKEVM_CASES)]
    fn pikevm(case: &Case) -> u64 {
        count(case.id, PIKEVM)
    }

    #[divan::bench(args = CASES)]
    fn boundedrecursor(case: &Case) -> u64 {
        count(case.id, BOUNDED_RECURSOR)
    }
}

mod regexvibe {
    use super::*;

    #[divan::bench(args = CASES)]
    fn refinedpikevm(case: &Case) -> u64 {
        count(case.id, REFINED_PIKEVM)
    }
}
