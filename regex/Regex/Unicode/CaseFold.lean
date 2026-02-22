import Std.Data.HashMap
import Std.Tactic.Do

open Std.Do

set_option mvcgen.warning false

set_option autoImplicit false

namespace Regex.Unicode

@[specialize]
def binarySearch {α} (c : Char) (values : Array α) (f : α → Char)
  (lo : Nat := 0) (hi : Nat := values.size) (le : hi ≤ values.size := by grind) : Nat :=
  if _ : lo ≥ hi then lo
  else
    let mid := (lo + hi) / 2
    have hmid : mid < values.size := by grind
    if c = f values[mid] then mid
    else if c < f values[mid] then
      binarySearch c values f lo mid (by grind)
    else
      binarySearch c values f (mid + 1) hi (by grind)
termination_by hi - lo

private def parseCaseFoldTable (s : String) : Array (Char × Char) := Id.run do
  let mut result : Array (Char × Char) := #[]
  let lines := s.splitOn "\n"
  for line in lines do
    if line.isEmpty then continue
    let parts := line.splitOn ";"
    if parts.length >= 2 then
      if let (some src, some tgt) := (parseHex parts[0]!, parseHex parts[1]!) then
        result := result.push (src, tgt)
  return result
where
  parseHex (s : String) : Option Char := do
    let s := s.trimAscii.toString
    if s.isEmpty then none
    else
      let n ← s.foldl (init := some 0) fun acc c =>
        acc.bind fun n =>
          let d := if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
                   else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
                   else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
                   else none
          d.map fun d => n * 16 + d
      if n.isValidChar then some (Char.ofNat n) else none

private def caseFoldData : String := include_str "../../data/Simple_Case_Folding.txt"

-- TODO: maybe representative table is a better name
def caseFoldRepresentatives : Thunk (Array (Char × Char)) :=
  Thunk.mk fun _ => parseCaseFoldTable caseFoldData

def buildCaseFoldInvMap (representatives : Array (Char × Char)) : Std.HashMap Char (Array Char) := Id.run do
  let mut table : Std.HashMap Char (Array Char) := {}
  for p in representatives do
    table := table.alter p.2 fun arr => (arr.getD #[]).push p.1
  return table

@[grind .]
theorem mem_buildCaseFoldInvMap_iff {c c' : Char} {rs : Array (Char × Char)} :
  (∃ _ : c' ∈ buildCaseFoldInvMap rs, c ∈ (buildCaseFoldInvMap rs)[c']) ↔ (c, c') ∈ rs := by
  generalize eq : buildCaseFoldInvMap rs = table
  apply Id.of_wp_run_eq eq; clear eq
  mvcgen invariants
  · ⇓⟨cursor, table⟩ =>
    ⌜(∃ _ : c' ∈ table, c ∈ table[c']) ↔ (c, c') ∈ cursor.prefix.toArray⌝
  case vc1.step pref cur suff eq table inv => grind
  case vc2.a.pre => simp

def caseFoldInvMap : Thunk (Std.HashMap Char (Array Char)) :=
  Thunk.mk fun _ => buildCaseFoldInvMap caseFoldRepresentatives.get

theorem mem_caseFoldInvMap_iff {c c' : Char} :
  (∃ _ : c' ∈ caseFoldInvMap.get, c ∈ caseFoldInvMap.get[c']) ↔ (c, c') ∈ caseFoldRepresentatives.get :=
  mem_buildCaseFoldInvMap_iff

/--
Returns the case-fold-equivalent characters for a given character.

The first return value corresponds to the representative character for the equivalence class,
and the second return value corresponds to the remaining characters in the equivalence class.
-/
def getCaseFoldEquivChars (c : Char) : (Char × Array Char) :=
  let table := caseFoldRepresentatives.get
  let idx := binarySearch c table (·.1) 0 table.size (by grind)
  if h : idx < table.size then
    let p := table[idx]
    if p.1 = c then
      have : p.2 ∈ caseFoldInvMap.get := (mem_buildCaseFoldInvMap_iff.mpr (by grind : (p.1, p.2) ∈ table)).1
      (p.2, caseFoldInvMap.get[p.2])
    else
      (c, caseFoldInvMap.get[c]?.getD #[])
  else
    (c, caseFoldInvMap.get[c]?.getD #[])

end Regex.Unicode
