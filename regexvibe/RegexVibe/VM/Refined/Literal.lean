module

public import Regex

/-!
Byte-string prefilter for patterns that are one literal or an alternation of
literals.

The PikeVM still confirms the match and records captures. The prefilter only
chooses the next position at which a match is allowed to start. A position is
skipped only when every match of the pattern consumes one of the needles there.
-/

public section

open String (Pos)

namespace RegexVibe.VM.Refined

/-- Reference scan. The C search replaces this at runtime. Not found returns the byte length. -/
@[extern "lean_regex_find_bytes"]
def findBytes (hay : @& String) (off : USize) (needle : @& ByteArray) : USize :=
  let hsz := hay.utf8ByteSize
  let nsz := needle.size
  let rec eqAt (nsz i k : Nat) : Bool :=
    if k = nsz then
      true
    else if hk : k < nsz then
      if hik : i + k < hay.utf8ByteSize then
        let raw : String.Pos.Raw := ⟨i + k⟩
        have hraw : raw < hay.rawEndPos := by
          simpa [String.Pos.Raw.lt_iff, String.byteIdx_rawEndPos] using hik
        match needle[k]? with
        | some b => hay.getUTF8Byte raw hraw == b && eqAt nsz i (k + 1)
        | none => false
      else
        false
    else
      false
  termination_by nsz - k
  let rec go (hsz nsz fuel i : Nat) : Nat :=
    match fuel with
    | 0 => hsz
    | fuel + 1 =>
      if i + nsz ≤ hsz then
        if eqAt nsz i 0 then i else go hsz nsz fuel (i + 1)
      else
        hsz
  if nsz = 0 || off.toNat > hsz || hsz < off.toNat + nsz then
    hsz.toUSize
  else
    (go hsz nsz (hsz + 1) off.toNat).toUSize

/-- Earliest needle offset at or after `off`, or the haystack length if none.

The C search is one pass. This body is the reference only.
-/
@[extern "lean_regex_find_earliest"]
def findEarliest (hay : @& String) (off : USize) (needles : @& Array ByteArray) : USize :=
  needles.foldl (init := hay.utf8ByteSize.toUSize) fun best n =>
    let i := findBytes hay off n
    if i < best then i else best

private def pushChar (b : ByteArray) (c : Char) : ByteArray :=
  b.append (String.singleton c).toByteArray

/--
Needles that every match must consume, read off the Thompson NFA.

`none` means the pattern is not a literal or an alternation of literals.
Saves and epsilons are ignored. A loop, anchor, or character class aborts.
An empty needle aborts too: the pattern can match without consuming input.
-/
def literalNeedles (nfa : Regex.NFA) : Option (Array ByteArray) :=
  let rec walk (fuel i : Nat) (buf : ByteArray) (path : List Nat) : Option (Array ByteArray) :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      if path.contains i then
        none
      else if h : i < nfa.size then
        match nfa[i] with
        | .done =>
          if buf.size = 0 then none else some #[buf]
        | .fail => some #[]
        | .epsilon next => walk fuel next buf (i :: path)
        | .save _ next => walk fuel next buf (i :: path)
        | .char c next => walk fuel next (pushChar buf c) (i :: path)
        | .split a b =>
          match walk fuel a buf (i :: path), walk fuel b buf (i :: path) with
          | some xs, some ys => some (xs ++ ys)
          | _, _ => none
        | .anchor _ _ => none
        | .sparse _ _ => none
      else
        none
  match walk (nfa.size + 1) nfa.start ByteArray.empty [] with
  | some ns =>
    if ns.isEmpty || ns.any (fun n => n.size = 0) then none else some ns
  | none => none

/-- A byte offset that is a UTF-8 boundary, as a `Pos`. -/
def posOfByte (s : String) (off : USize) : Option (Pos s) :=
  if hlt : off.toNat < s.utf8ByteSize then
    let raw : String.Pos.Raw := ⟨off.toNat⟩
    have hraw : raw < s.rawEndPos := by
      simpa [String.Pos.Raw.lt_iff, String.byteIdx_rawEndPos] using hlt
    if hbyte : (s.getUTF8Byte raw hraw).IsUTF8FirstByte then
      some ⟨raw, (String.Pos.Raw.isValid_iff_isUTF8FirstByte).mpr (Or.inr ⟨hraw, hbyte⟩)⟩
    else
      none
  else
    none

/-- Next position at which a literal match may start, if any needle occurs. -/
def earliestPos (hay : String) (start : Pos hay) (needles : Array ByteArray) : Option (Pos hay) :=
  let found := findEarliest hay start.offset.byteIdx.toUSize needles
  posOfByte hay found

end RegexVibe.VM.Refined
