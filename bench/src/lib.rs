//! FFI to the three matchers exported by `RegexVibe.BenchFFI`.
//!
//! * `0` — `regex/pikevm`
//! * `1` — `regex/boundedrecursor`
//! * `2` — `regexvibe/refinedpikevm`

use std::ffi::{CStr, CString};
use std::os::raw::c_char;
use std::path::Path;
use std::sync::{Mutex, Once};

pub const PIKEVM: u32 = 0;
pub const BOUNDED_RECURSOR: u32 = 1;
pub const REFINED_PIKEVM: u32 = 2;

unsafe extern "C" {
    fn regex_bench_startup(dir: *const c_char) -> i32;
    fn regex_bench_cases() -> u32;
    fn regex_bench_matches(case_id: u32, engine: u32) -> u64;
    fn regex_bench_name(case_id: u32) -> *const c_char;
}

static LOCK: Mutex<()> = Mutex::new(());
static START: Once = Once::new();

fn ensure_started() {
    START.call_once(|| {
        let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../regexvibe/bench/rebar/haystacks");
        let dir = CString::new(dir.to_string_lossy().as_bytes()).expect("haystack path");
        let rc = unsafe { regex_bench_startup(dir.as_ptr()) };
        if rc != 0 {
            panic!("regex_bench_startup failed with status {rc}");
        }
    });
}

/// Compile the curated patterns and load clipped haystacks. Safe to call more than once.
pub fn startup() {
    let _guard = LOCK.lock().expect("benchmark lock");
    ensure_started();
}

pub fn n_cases() -> u32 {
    let _guard = LOCK.lock().expect("benchmark lock");
    ensure_started();
    unsafe { regex_bench_cases() }
}

pub fn case_name(case_id: u32) -> String {
    let _guard = LOCK.lock().expect("benchmark lock");
    ensure_started();
    read_name(case_id)
}

fn read_name(case_id: u32) -> String {
    let ptr = unsafe { regex_bench_name(case_id) };
    if ptr.is_null() {
        return String::new();
    }
    unsafe { CStr::from_ptr(ptr) }
        .to_string_lossy()
        .into_owned()
}

pub fn count(case_id: u32, engine: u32) -> u64 {
    let _guard = LOCK.lock().expect("benchmark lock");
    ensure_started();
    unsafe { regex_bench_matches(case_id, engine) }
}

pub fn case_id(name: &str) -> u32 {
    let _guard = LOCK.lock().expect("benchmark lock");
    ensure_started();
    let n = unsafe { regex_bench_cases() };
    for i in 0..n {
        if read_name(i) == name {
            return i;
        }
    }
    panic!("no benchmark case named {name}");
}
