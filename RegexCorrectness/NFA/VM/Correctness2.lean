import RegexCorrectness.NFA.VM.Traversal
import RegexCorrectness.NFA.Transition

namespace NFA

theorem pathIn_of_reaches {nfa : NFA} {i : Fin nfa.nodes.size} {m : List Char}
  (h : nfa.reaches i m) :
  nfa.pathIn 0 nfa.start i m := by
  induction h with
  | nil cls => simp [pathIn_iff_εClosure.mpr cls]
  | @snoc i j k c m _ step cls ih =>
    simp [charStep] at step
    have ih' : nfa.pathIn (min 0 j) nfa.start j (m ++ [c]) :=
      ih.snoc_char i.isLt step
    simp at ih'
    have := ih'.trans (pathIn_iff_εClosure.mpr cls)
    simp at this
    exact this

theorem stepIn.nil_or_singleton {start} (h : stepIn nfa start i j cs) :
  cs = [] ∨ ∃ c, cs = [c] := by
  cases h with
  | εStep => exact .inl rfl
  | charStep => exact .inr ⟨_, rfl⟩

theorem stepIn.nil_of_snoc {start} (h : stepIn nfa start i j (cs ++ [c])) :
  cs = [] := by
  generalize h' : cs ++ [c] = cs' at h
  cases h with
  | εStep => simp at h'
  | charStep =>
    cases cs with
    | nil => rfl
    | cons _ _ =>
      have := congrArg List.length h'
      simp at this

theorem pathIn.of_snoc_char {start}
  (path : pathIn nfa start i l (cs ++ [c])) :
  ∃ j k, pathIn nfa start i j cs ∧ k ∈ nfa.charStep j c ∧ l ∈ nfa.εClosure k := by
  generalize h : cs ++ [c] = cs' at path
  induction path generalizing cs with
  | base _ => simp at h
  | @step i j k cs₁ cs₂ step rest ih =>
    match snoc_eq_append h with
    | .inl ⟨h₁, h₂⟩ =>
      simp [h₁, h₂] at step rest
      have := step.nil_of_snoc
      simp [this] at *
      cases step with
      | charStep le _ step =>
        exact ⟨i, .base le, j, charStep_of_charStep step, εClosure_of_pathIn rest⟩
    | .inr ⟨cs₂', h₁, h₂⟩ =>
      have ⟨j', k', path', step', cls⟩ := ih h₂.symm
      exact ⟨j', k', h₁ ▸ .step step path', step', cls⟩
where
  snoc_eq_append {cs₁ cs₂ cs₃ : List Char} {c : Char} (h : cs₁ ++ [c] = cs₂ ++ cs₃) :
    (cs₂ = cs₁ ++ [c] ∧ cs₃ = []) ∨ (∃ cs₃', cs₁ = cs₂ ++ cs₃' ∧ cs₃ = cs₃' ++ [c]) := by
    cases cs₃ using List.list_reverse_induction with
    | base =>
      simp at h
      exact .inl ⟨h.symm, rfl⟩
    | ind cs₃ c' =>
      have : c = c' ∧ cs₁ = cs₂ ++ cs₃ := by
        have h₁ := congrArg List.reverse h
        simp at h₁
        have h₂ := congrArg List.reverse h₁.right
        simp at h₂
        exact ⟨h₁.left, h₂⟩
      simp [this]

theorem reaches_of_pathIn {nfa : NFA} {i : Fin nfa.nodes.size} {m : List Char}
  (h : nfa.pathIn 0 nfa.start i m) :
  nfa.reaches i m := by
  induction m using List.list_reverse_induction generalizing i with
  | base => exact .nil (pathIn_iff_εClosure.mp h)
  | ind m c ih =>
    have ⟨j, k, path, step, cls⟩ := pathIn.of_snoc_char h
    let j' : Fin nfa.nodes.size := ⟨j, path.lt_right nfa.start.isLt⟩
    have prev := ih (i := j') path
    exact .snoc prev step cls

theorem reaches_iff_pathIn {nfa : NFA} {i : Fin nfa.nodes.size} {m : List Char} :
  nfa.reaches i m ↔ nfa.pathIn 0 nfa.start i m := ⟨pathIn_of_reaches, reaches_of_pathIn⟩

theorem matches_of_reaches (eq : compile r = nfa)
  (h₁ : nfa.reaches i cs.data) (h₂ : nfa[i] = .done) :
  r.matches cs := by
  have hi : i.val = 0 := (done_iff_zero_compile eq i).mp h₂
  have : nfa.pathIn 0 nfa.start i cs.data := pathIn_of_reaches h₁
  simp at this
  have := pathToNext_of_compile_of_pathIn eq (hi ▸ this)
  exact (matches_iff_pathToNext eq).mpr this

theorem reaches_of_matches (eq : compile r = nfa)
  (m : r.matches cs) :
  ∃ i, nfa.reaches i cs.data ∧ nfa[i] = .done := by
  have := (matches_iff_pathToNext eq).mp m
  have := pathIn_of_pathToNext this
  simp at this
  let i' : Fin nfa.nodes.size := ⟨0, lt_zero_size_compile eq⟩
  have := reaches_of_pathIn (i := i') this
  have hdone := (done_iff_zero_compile eq i').mpr rfl
  exact ⟨i', this, hdone⟩

theorem matches_iff_reaches (eq : compile r = nfa) :
  r.matches cs ↔ ∃ i, nfa.reaches i cs.data ∧ nfa[i] = .done :=
  ⟨reaches_of_matches eq, fun ⟨_, h₁, h₂⟩ => matches_of_reaches eq h₁ h₂⟩

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
