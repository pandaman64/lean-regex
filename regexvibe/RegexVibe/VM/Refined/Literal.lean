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

/-- Byte length. The C version reads the string header. -/
@[extern "lean_regex_utf8_len"]
def utf8LenFast (s : String) : USize :=
  s.utf8ByteSize.toUSize

@[expose, implemented_by utf8LenFast]
def utf8Len (s : String) : USize :=
  s.utf8ByteSize.toUSize

/-- Code point at a byte offset. The C version does not allocate. -/
@[extern "lean_regex_utf8_get_off"]
def getOff (s : String) (i : USize) : UInt32 :=
  if h : i.toNat < s.utf8ByteSize then
    let raw : String.Pos.Raw := ⟨i.toNat⟩
    have hraw : raw < s.rawEndPos := by
      simpa [String.Pos.Raw.lt_iff, String.byteIdx_rawEndPos] using h
    s.getUTF8Byte raw hraw |>.toUInt32
  else
    0

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

theorem posOfByte_index {s : String} {i : USize} {p : Pos s} (h : posOfByte s i = some p) :
    p.offset.byteIdx = i.toNat := by
  simp only [posOfByte] at h
  split at h
  · next =>
    split at h
    · next =>
      cases h
      rfl
    · cases h
  · cases h

theorem not_end_of_lt {s : String} {i : USize}
    (hvalid : (⟨i.toNat⟩ : String.Pos.Raw).IsValid s) (hlt : i.toNat < s.utf8ByteSize) :
    (⟨⟨i.toNat⟩, hvalid⟩ : Pos s) ≠ s.endPos := by
  intro heq
  have hidx : (⟨⟨i.toNat⟩, hvalid⟩ : Pos s).offset.byteIdx = i.toNat := rfl
  have hend : (⟨⟨i.toNat⟩, hvalid⟩ : Pos s).offset.byteIdx = s.utf8ByteSize := by
    have := congrArg (fun q : Pos s => q.offset.byteIdx) heq
    simpa [String.byteIdx_rawEndPos] using this
  omega

/-- Next character boundary, as a byte index. An offset that is not a boundary jumps to the end. -/
def nextByte (s : String) (i : USize) : Nat :=
  if h : i.toNat < s.utf8ByteSize then
    let raw : String.Pos.Raw := ⟨i.toNat⟩
    if hvalid : raw.IsValid s then
      let p : Pos s := ⟨raw, hvalid⟩
      (p.next (not_end_of_lt hvalid h)).offset.byteIdx
    else
      s.utf8ByteSize
  else
    i.toNat

/-- Next character boundary. Proofs see this body; the compiled code is the C walk. -/
def nextOffSpec (s : String) (i : USize) : USize :=
  (nextByte s i).toUSize

@[extern "lean_regex_utf8_next_off"]
def nextOffFast (s : String) (i : USize) : USize :=
  nextOffSpec s i

@[implemented_by nextOffFast]
def nextOff (s : String) (i : USize) : USize :=
  nextOffSpec s i

theorem nextByte_progress (s : String) (i : USize) (h : i.toNat < s.utf8ByteSize) :
    i.toNat < nextByte s i ∧ nextByte s i ≤ s.utf8ByteSize := by
  unfold nextByte
  rw [dite_eq_left h]
  by_cases hvalid : (⟨i.toNat⟩ : String.Pos.Raw).IsValid s
  · rw [dite_eq_left hvalid]
    let p : Pos s := ⟨⟨i.toNat⟩, hvalid⟩
    have hne : p ≠ s.endPos := not_end_of_lt hvalid h
    have hlt : p.offset.byteIdx < (p.next hne).offset.byteIdx := by
      have := p.lt_next (h := hne)
      simpa [String.Pos.lt_iff, String.Pos.Raw.lt_iff] using this
    have hle : (p.next hne).offset.byteIdx ≤ s.utf8ByteSize := by
      have hv := (p.next hne).isValid.le_rawEndPos
      simpa [String.Pos.Raw.le_iff, String.byteIdx_rawEndPos] using hv
    constructor
    · simpa using hlt
    · exact hle
  · rw [dite_eq_right hvalid]
    exact ⟨h, Nat.le_refl _⟩

theorem nextOff_progress (s : String) (i : USize) (h : i.toNat < s.utf8ByteSize)
    (h64 : s.utf8ByteSize < USize.size) :
    i.toNat < (nextOff s i).toNat ∧ (nextOff s i).toNat ≤ s.utf8ByteSize := by
  have hdef : nextOff s i = (nextByte s i).toUSize := by
    unfold nextOff nextOffSpec
    rfl
  have hprog := nextByte_progress s i h
  have hlt64 : nextByte s i < USize.size := Nat.lt_of_le_of_lt hprog.2 h64
  have hnat : (nextByte s i).toUSize.toNat = nextByte s i := USize.toNat_ofNat_of_lt hlt64
  rw [hdef, hnat]
  exact hprog

/-- `utf8ByteSize + 1 < 2^64` puts the length inside a 64-bit `USize`. -/
theorem byteSize_lt_usize {s : String} (h : s.utf8ByteSize + 1 < 2 ^ 64) :
    s.utf8ByteSize < USize.size := by
  rw [USize.size_eq_two_pow]
  cases System.Platform.numBits_eq with
  | inr h64 =>
    rw [h64]
    omega
  | inl h32 =>
    have h64 : System.Platform.numBits = 64 := by native_decide
    simp [h32] at h64

theorem nextOff_pos {s : String} {i : USize} (hp : ∃ p : Pos s, p.offset.byteIdx = i.toNat)
    (hlt : i.toNat < s.utf8ByteSize) (hsz : s.utf8ByteSize < USize.size) :
    ∃ q : Pos s, q.offset.byteIdx = (nextOff s i).toNat := by
  rcases hp with ⟨p, hp⟩
  have hdef : nextOff s i = (nextByte s i).toUSize := by
    unfold nextOff nextOffSpec
    rfl
  have hprog := nextByte_progress s i hlt
  have hlt64 : nextByte s i < USize.size := Nat.lt_of_le_of_lt hprog.2 hsz
  have hnat : (nextByte s i).toUSize.toNat = nextByte s i := USize.toNat_ofNat_of_lt hlt64
  unfold nextByte at hnat hdef
  rw [dite_eq_left hlt] at hnat hdef
  have hraw : (⟨i.toNat⟩ : String.Pos.Raw) = p.offset := by
    apply String.Pos.Raw.ext
    simpa using hp.symm
  have hvalid : (⟨i.toNat⟩ : String.Pos.Raw).IsValid s := by
    rw [hraw]
    exact p.isValid
  rw [dite_eq_left hvalid] at hnat hdef
  let q : Pos s := ⟨⟨i.toNat⟩, hvalid⟩
  refine ⟨q.next (not_end_of_lt hvalid hlt), ?_⟩
  rw [hdef, hnat]

theorem pos_end {s : String} {off : USize} (h : off.toNat = s.utf8ByteSize) :
    ∃ p : Pos s, p.offset.byteIdx = off.toNat :=
  ⟨s.endPos, by rw [h]; simp [String.byteIdx_rawEndPos]⟩

theorem pos_of_pos {s : String} (p : Pos s) (h : p.offset.byteIdx < USize.size) :
    ∃ q : Pos s, q.offset.byteIdx = p.offset.byteIdx.toUSize.toNat := by
  refine ⟨p, ?_⟩
  exact (USize.toNat_ofNat_of_lt h).symm

/-- Next position at which a literal match may start, if any needle occurs. -/
def earliestPos (hay : String) (start : Pos hay) (needles : Array ByteArray) : Option (Pos hay) :=
  let found := findEarliest hay start.offset.byteIdx.toUSize needles
  posOfByte hay found

end RegexVibe.VM.Refined
