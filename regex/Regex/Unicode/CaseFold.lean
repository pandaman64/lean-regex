import Std.Data.HashMap

set_option autoImplicit false

namespace Regex.Unicode

@[specialize]
private def binarySearch {α} [Inhabited α] (c : UInt32) (values : Array α) (f : α → UInt32) (lo hi : Nat) : Nat :=
  if lo >= hi then lo
  else
    let mid := (lo + hi) / 2
    if lo = mid then lo
    else if c < f values[mid]! then
      binarySearch c values f lo mid
    else
      binarySearch c values f mid hi
termination_by hi - lo

private def parseCaseFoldTable (s : String) : Array (UInt32 × UInt32) := Id.run do
  let mut result : Array (UInt32 × UInt32) := #[]
  let lines := s.splitOn "\n"
  for line in lines do
    if line.isEmpty then continue
    let parts := line.splitOn ";"
    if parts.length >= 2 then
      if let (some src, some tgt) := (parseHex parts[0]!, parseHex parts[1]!) then
        result := result.push (src, tgt)
  return result
where
  parseHex (s : String) : Option UInt32 :=
    let s := s.trimAscii.toString
    if s.isEmpty then none
    else
      s.foldl (init := some (0 : UInt32)) fun acc c =>
        acc.bind fun n =>
          let d := if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
                   else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
                   else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
                   else none
          d.map fun d => n * 16 + d.toUInt32

private def caseFoldData : String := include_str "../../data/Simple_Case_Folding.txt"

private def caseFoldTableThunk : Thunk (Array (UInt32 × UInt32)) :=
  Thunk.mk fun _ => parseCaseFoldTable caseFoldData

def caseFoldTable : Array (UInt32 × UInt32) := caseFoldTableThunk.get

def getCaseFoldChar (c : Char) : Char :=
  if c.val < 0x41 then c
  else if c.val <= 0x5A then
    Char.ofNat (c.toNat + 0x20)
  else if c.val < 0x80 then c
  else
    let table := caseFoldTable
    if table.isEmpty then c
    else
      let idx := binarySearch c.val table (·.1) 0 table.size
      if h : idx < table.size then
        let (src, tgt) := table[idx]
        if src == c.val then
          Char.ofNat tgt.toNat
        else c
      else c

def insertCaseFoldEquiv (result : Std.HashMap UInt32 (Array UInt32)) (pair : UInt32 × UInt32) :
    Std.HashMap UInt32 (Array UInt32) :=
  let (src, tgt) := pair
  match result[tgt]? with
  | some arr => result.insert tgt (arr.push src)
  | none => result.insert tgt #[tgt, src]

def buildCaseFoldEquivTable : Std.HashMap UInt32 (Array UInt32) :=
  caseFoldTable.toList.foldl insertCaseFoldEquiv {}

private def caseFoldEquivTableThunk : Thunk (Std.HashMap UInt32 (Array UInt32)) :=
  Thunk.mk fun _ => buildCaseFoldEquivTable

def caseFoldEquivTable : Std.HashMap UInt32 (Array UInt32) := caseFoldEquivTableThunk.get

def getCaseFoldEquivChars (c : Char) : Array Char :=
  let folded := getCaseFoldChar c
  match caseFoldEquivTable[folded.val]? with
  | some arr => arr.map fun u => Char.ofNat u.toNat
  | none =>
    if folded == c then
      #[folded]
    else
      #[folded, c]

end Regex.Unicode
