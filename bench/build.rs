use std::env;
use std::path::{Path, PathBuf};
use std::process::Command;

fn main() {
    let manifest = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    let repo = manifest.parent().unwrap().to_path_buf();
    let regexvibe = repo.join("regexvibe");
    let regex = repo.join("regex");

    println!("cargo:rerun-if-changed=src/shim.c");
    println!("cargo:rerun-if-changed=build.rs");
    println!(
        "cargo:rerun-if-changed={}",
        regexvibe.join("RegexVibe").display()
    );
    println!("cargo:rerun-if-changed={}", regexvibe.join("c").display());
    println!(
        "cargo:rerun-if-changed={}",
        regexvibe.join("lakefile.lean").display()
    );
    println!("cargo:rerun-if-changed={}", regex.join("Regex").display());
    println!(
        "cargo:rerun-if-changed={}",
        regex.join("lakefile.toml").display()
    );

    let lake = lake_exe();
    let status = Command::new(&lake)
        .current_dir(&regexvibe)
        .args([
            "build",
            "RegexBench:static",
            "RegexVibe:static",
            "Regex:static",
            "libbytearray_wide_ffi",
        ])
        .status()
        .unwrap_or_else(|err| panic!("failed to run {}: {err}", lake.display()));
    if !status.success() {
        panic!("lake build failed");
    }

    let bench_a = regexvibe.join(".lake/build/lib/libRegexVibe_RegexBench.a");
    let vibe_a = regexvibe.join(".lake/build/lib/libRegexVibe_RegexVibe.a");
    let regex_a = regex.join(".lake/build/lib/libRegex_Regex.a");
    let ffi_a = regexvibe.join(".lake/build/lib/libbytearray_wide_ffi.a");
    for path in [&bench_a, &vibe_a, &regex_a, &ffi_a] {
        if !path.exists() {
            panic!("missing static library {}", path.display());
        }
    }

    let lean_prefix = lean_prefix(&lake);
    let init = find_init_symbol(&bench_a);
    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
    let so = out_dir.join("libregex_bench.so");
    let leanc = lean_prefix.join("bin/leanc");
    let lean_lib = lean_prefix.join("lib/lean");

    let status = Command::new(&leanc)
        .arg("-shared")
        .arg("-flto")
        .arg("-O3")
        .arg("-fno-semantic-interposition")
        .arg("-o")
        .arg(&so)
        .arg("-Wl,--whole-archive")
        .arg(&bench_a)
        .arg(&vibe_a)
        .arg(&regex_a)
        .arg(&ffi_a)
        .arg("-Wl,--no-whole-archive")
        .arg(format!("-Wl,-rpath,{}", lean_lib.display()))
        .status()
        .unwrap_or_else(|err| panic!("failed to run {}: {err}", leanc.display()));
    if !status.success() {
        panic!("leanc -shared failed");
    }

    let mut cc = cc::Build::new();
    cc.file(manifest.join("src/shim.c"));
    cc.include(lean_prefix.join("include"));
    cc.define("REGEX_BENCH_INIT", Some(init.as_str()));
    cc.flag("-fPIC");
    cc.compile("regex_bench_shim");

    println!("cargo:rustc-link-search=native={}", out_dir.display());
    println!("cargo:rustc-link-lib=dylib=regex_bench");
    println!("cargo:rustc-link-search=native={}", lean_lib.display());
    println!("cargo:rustc-link-lib=dylib=leanshared");
    println!("cargo:rustc-link-arg=-Wl,-rpath,{}", out_dir.display());
    println!("cargo:rustc-link-arg=-Wl,-rpath,{}", lean_lib.display());
}

fn lake_exe() -> PathBuf {
    if let Some(path) = env::var_os("LAKE") {
        return PathBuf::from(path);
    }
    if let Ok(path) = which_on_path("lake") {
        return path;
    }
    if let Ok(home) = env::var("HOME") {
        let elan = PathBuf::from(home).join(".elan/bin/lake");
        if elan.exists() {
            return elan;
        }
    }
    PathBuf::from("lake")
}

fn which_on_path(name: &str) -> Result<PathBuf, ()> {
    let path = env::var_os("PATH").ok_or(())?;
    for dir in env::split_paths(&path) {
        let candidate = dir.join(name);
        if candidate.is_file() {
            return Ok(candidate);
        }
    }
    Err(())
}

fn lean_prefix(lake: &Path) -> PathBuf {
    let output = Command::new(lake)
        .current_dir(env::var("CARGO_MANIFEST_DIR").unwrap() + "/../regexvibe")
        .arg("env")
        .arg("lean")
        .arg("--print-prefix")
        .output()
        .unwrap_or_else(|err| panic!("lean --print-prefix failed to start: {err}"));
    if !output.status.success() {
        panic!(
            "lean --print-prefix failed: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    PathBuf::from(String::from_utf8_lossy(&output.stdout).trim())
}

fn find_init_symbol(archive: &Path) -> String {
    let output = Command::new("strings")
        .arg(archive)
        .output()
        .unwrap_or_else(|err| panic!("strings failed: {err}"));
    if !output.status.success() {
        panic!(
            "strings {} failed: {}",
            archive.display(),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    let text = String::from_utf8_lossy(&output.stdout);
    let mut runtime = None;
    let mut i = 0;
    while let Some(rel) = text[i..].find("initialize_") {
        let start = i + rel;
        let end = text[start..]
            .find(|c: char| !c.is_ascii_alphanumeric() && c != '_')
            .map(|off| start + off)
            .unwrap_or(text.len());
        let sym = &text[start..end];
        if sym.contains("BenchFFI") {
            if sym.starts_with("initialize_") && !sym.contains("runtime_") && !sym.contains("meta_")
            {
                return sym.to_string();
            }
            if sym.starts_with("runtime_initialize_") {
                runtime = Some(sym.to_string());
            }
        }
        i = end.max(start + 1);
    }
    runtime.unwrap_or_else(|| panic!("no BenchFFI initializer in {}", archive.display()))
}
