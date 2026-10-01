import Lake
open System Lake DSL

/-!
`lakefile.toml` converted so the wide `ByteArray` reader can be built and
linked the way lean-zip does (see `lakefile.lean` there, and lean#14053).

`-flto` lets the link inline `c/bytearray_wide_ffi.c` into the PikeVM loop.
Every object must come from the same compiler: Lean-emitted C already uses
the toolchain compiler, and the FFI target uses `buildLeanO` for that same
compiler. `-fno-semantic-interposition` keeps `-fPIC` from blocking the
cross-object inline. Linux-only. Set `REGEX_LTO=0` to opt out; Lake caches
`run_io` config, so reconfigure with `lake -R build` after toggling it.
-/

def ltoFlags : IO (Array String) := do
  if Platform.isWindows || Platform.isOSX then return #[]
  if (← IO.getEnv "REGEX_LTO") == some "0" then return #[]
  return #["-flto", "-fno-semantic-interposition"]

/-- Link-side LTO. `-O3` matches the per-module `relWithDebInfo` compiles. -/
def ltoLinkFlags : IO (Array String) := do
  let flags ← ltoFlags
  if flags.isEmpty then return #[] else return flags ++ #["-O3"]

package Regex where
  version := v!"0.1.0"
  keywords := #["regex"]
  testDriver := "RegexTest"
  leanOptions := #[⟨`autoImplicit, false⟩]
  moreLeancArgs := run_io ltoFlags
  moreLinkArgs := run_io ltoLinkFlags

@[default_target]
lean_lib Regex where
  buildType := .relWithDebInfo

lean_lib RegexTest where
  globs := #[.submodules `tests]

-- Little-endian UInt32 load/store on ByteArray. No external library.
input_file bytearray_wide_ffi.c where
  path := "c" / "bytearray_wide_ffi.c"
  text := true

target bytearray_wide_ffi.o pkg : FilePath := do
  let srcJob ← bytearray_wide_ffi.c.fetch
  let oFile := pkg.buildDir / "c" / "bytearray_wide_ffi.o"
  -- `-O2` folds the byte-wise reference sequence into one load. `-DNDEBUG`
  -- matches the release runtime: the bounds live in the Lean reference body.
  -- `-flto` bitcode is produced by the toolchain compiler via `buildLeanO`.
  let hardArgs := #["-O2", "-DNDEBUG"] ++ (← ltoFlags) ++
    if Platform.isWindows then #[] else #["-fPIC"]
  buildLeanO oFile srcJob #[] hardArgs

extern_lib libbytearray_wide_ffi pkg := do
  let ffiO ← bytearray_wide_ffi.o.fetch
  let name := nameToStaticLib "bytearray_wide_ffi"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

lean_exe Bench where
  srcDir := "scripts"
  buildType := .relWithDebInfo

lean_exe GenSimpleCaseFolding where
  srcDir := "scripts"

lean_exe CorpusTest where
  srcDir := "tests"
