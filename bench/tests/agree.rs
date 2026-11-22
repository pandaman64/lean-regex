use lean_regex_bench::{case_name, count, n_cases, BOUNDED_RECURSOR, PIKEVM, REFINED_PIKEVM};

const NAMES: &[&str] = &[
    "curated/literal/sherlock-en",
    "curated/literal/sherlock-casei-en",
    "curated/literal/sherlock-zh",
    "curated/literal-alternate/sherlock-en",
    "curated/words/all-english",
    "curated/bounded-repeat/letters-en",
    "curated/cloud-flare-redos/simplified-long",
];

#[test]
fn engines_agree_on_every_case() {
    let n = n_cases();
    assert_eq!(n as usize, NAMES.len());
    for i in 0..n {
        let name = case_name(i);
        assert_eq!(name, NAMES[i as usize]);
        let pike = count(i, PIKEVM);
        let bounded = count(i, BOUNDED_RECURSOR);
        let refined = count(i, REFINED_PIKEVM);
        assert_eq!(pike, bounded, "{name}: pikevm vs boundedrecursor");
        assert_eq!(bounded, refined, "{name}: boundedrecursor vs refinedpikevm");
        assert!(pike > 0, "{name}: expected at least one match, got 0");
    }
}
