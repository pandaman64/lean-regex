import RegexCorrectness.NFA.VM.Traversal
import RegexCorrectness.NFA.Transition

namespace NFA

theorem pathIn_of_reaches {nfa : NFA} {i : Fin nfa.nodes.size} {m r : List Char}
  (h : nfa.reaches i m) :
  nfa.pathIn 0 nfa.start (m ++ r) i r := by
  induction h generalizing r with
  | nil cls => simp [pathIn_iff_εClosure.mpr cls]
  | @snoc i j k c m _ step cls ih =>
    simp
    simp [charStep] at step
    have ih' : nfa.pathIn (min 0 j) nfa.start (m ++ c :: r) j r :=
      ih.snoc_char i.isLt rfl step
    simp at ih'
    exact ih'.trans (pathIn_iff_εClosure.mpr cls)

theorem matches_of_reaches (eq : compile r = nfa)
  (h₁ : nfa.reaches i cs.data) (h₂ : nfa[i] = .done) :
  r.matches cs := by
  have hi : i.val = 0 := (done_iff_zero_compile eq i).mp h₂
  have : nfa.pathIn 0 nfa.start (cs.data ++ []) i [] := pathIn_of_reaches (r := []) h₁
  simp at this
  have := pathToNext_of_compile_of_pathIn eq (hi ▸ this)
  have ⟨cs', eqs, m⟩ := (matches_prefix_iff_pathToNext eq).mpr this
  have := String.ext_iff.mp eqs
  simp at this
  have := String.ext this
  exact this ▸ m

theorem matches_of_captureNext
  (eq : compile re = nfa)
  (h : captureNext nfa it saveSize = matched)
  (v : it.Valid)
  (hsome : matched.isSome) :
  ∃ (s : Substring) (l m r : List Char),
    s.ValidFor l m r ∧ it.toString = ⟨l ++ m ++ r⟩ ∧ re.matches ⟨m⟩ := by
  have ⟨s, l, m, r, sv, eqs, i, hr, hdone⟩ := captureNext_spec h v hsome
  have ma := matches_of_reaches eq hr hdone
  exact ⟨s, l, m, r, sv, eqs, ma⟩

end NFA
