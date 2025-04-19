import RegexCorrectness.Backtracker.Basic

set_option autoImplicit false

namespace Regex.Backtracker.captureNextAux

variable {σ nfa wf it startIdx maxIdx visited stack update visited'}

theorem mem_of_mem_visited {s i} (hmem : visited.get s i) :
  (captureNextAux σ nfa wf startIdx maxIdx visited stack).2.get s i := by
  induction visited, stack using captureNextAux.induct' σ nfa wf startIdx maxIdx with
  | base visited => simp [hmem]
  | visited visited update state it eq stack' mem ih => simp [mem, ih hmem]
  | done visited update state bit eq stack' mem hn => simp [mem, hn, BitMatrix.get_set, hmem]
  | fail visited update state bit eq stack' mem hn => simp [mem, hn, BitMatrix.get_set, hmem]
  | epsilon visited update state it eq stack' mem visited' state' hn ih =>
    rw [captureNextAux_epsilon mem hn]
    exact ih (by simp [visited', BitMatrix.get_set, hmem])
  | split visited update state it eq stack' mem visited' state₁ state₂ hn ih =>
    rw [captureNextAux_split mem hn]
    exact ih (by simp [visited', BitMatrix.get_set, hmem])
  | save visited update state it eq stack' mem visited' offset state' hn update' ih =>
    rw [captureNextAux_save mem hn]
    exact ih (by simp [visited', BitMatrix.get_set, hmem])
  | anchor_pos visited update state it eq stack' mem visited' a state' hn ht ih =>
    rw [captureNextAux_anchor_pos mem hn ht]
    exact ih (by simp [visited', BitMatrix.get_set, hmem])
  | anchor_neg visited update state it eq stack' mem visited' a state' hn ht ih =>
    rw [captureNextAux_anchor_neg mem hn ht]
    exact ih (by simp [visited', BitMatrix.get_set, hmem])
  | char_pos visited update state it eq stack' mem visited' c state' hn hnext hc ih =>
    rw [captureNextAux_char_pos mem hn hnext hc]
    exact ih (by simp [visited', BitMatrix.get_set, hmem])
  | char_neg visited update state it eq stack' mem visited' c state' hn hnext hc ih =>
    rw [captureNextAux_char_neg mem hn hnext hc]
    exact ih (by simp [visited', BitMatrix.get_set, hmem])
  | char_end visited update state it eq stack' mem visited' c state' hn hnext ih =>
    rw [captureNextAux_char_end mem hn hnext]
    exact ih (by simp [visited', BitMatrix.get_set, hmem])
  | sparse_pos visited update state it eq stack' mem visited' cs state' hn hnext hc ih =>
    rw [captureNextAux_sparse_pos mem hn hnext hc]
    exact ih (by simp [visited', BitMatrix.get_set, hmem])
  | sparse_neg visited update state it eq stack' mem visited' cs state' hn hnext hc ih =>
    rw [captureNextAux_sparse_neg mem hn hnext hc]
    exact ih (by simp [visited', BitMatrix.get_set, hmem])
  | sparse_end visited update state it eq stack' mem visited' cs state' hn hnext ih =>
    rw [captureNextAux_sparse_end mem hn hnext]
    exact ih (by simp [visited', BitMatrix.get_set, hmem])

theorem mem_of_mem_top_stack {entry stack'} (hstack : entry :: stack' = stack) :
  (captureNextAux σ nfa wf startIdx maxIdx visited stack).2.get entry.state (entry.it.index' entry.eq) := by
  induction visited, stack using captureNextAux.induct' σ nfa wf startIdx maxIdx with
  | base visited => simp at hstack
  | visited visited update state it eq stack' mem ih =>
    simp [mem]
    simp at hstack
    exact mem_of_mem_visited (by simp [hstack, mem])
  | done visited update state bit eq stack' mem hn =>
    simp [mem, hn]
    simp at hstack
    simp [hstack, BitMatrix.get_set]
  | fail visited update state bit eq stack' mem hn =>
    simp [mem, hn]
    simp at hstack
    simp [hstack, BitMatrix.get_set]
  | epsilon visited update state it eq stack'' mem visited' state' hn ih =>
    rw [captureNextAux_epsilon mem hn]
    simp at hstack
    exact mem_of_mem_visited (by simp [BitMatrix.get_set, hstack, mem])
  | split visited update state it eq stack'' mem visited' state₁ state₂ hn ih =>
    rw [captureNextAux_split mem hn]
    simp at hstack
    exact mem_of_mem_visited (by simp [BitMatrix.get_set, hstack, mem])
  | save visited update state it eq stack' mem visited' offset state' hn update' ih =>
    rw [captureNextAux_save mem hn]
    simp at hstack
    exact mem_of_mem_visited (by simp [BitMatrix.get_set, hstack, mem])
  | anchor_pos visited update state it eq stack' mem visited' a state' hn ht ih =>
    rw [captureNextAux_anchor_pos mem hn ht]
    simp at hstack
    exact mem_of_mem_visited (by simp [BitMatrix.get_set, hstack, mem])
  | anchor_neg visited update state it eq stack' mem visited' a state' hn ht ih =>
    rw [captureNextAux_anchor_neg mem hn ht]
    simp at hstack
    exact mem_of_mem_visited (by simp [BitMatrix.get_set, hstack, mem])
  | char_pos visited update state it eq stack' mem visited' c state' hn hnext hc ih =>
    rw [captureNextAux_char_pos mem hn hnext hc]
    simp at hstack
    exact mem_of_mem_visited (by simp [BitMatrix.get_set, hstack, mem])
  | char_neg visited update state it eq stack' mem visited' c state' hn hnext hc ih =>
    rw [captureNextAux_char_neg mem hn hnext hc]
    simp at hstack
    exact mem_of_mem_visited (by simp [BitMatrix.get_set, hstack, mem])
  | char_end visited update state it eq stack' mem visited' c state' hn hnext ih =>
    rw [captureNextAux_char_end mem hn hnext]
    simp at hstack
    exact mem_of_mem_visited (by simp [BitMatrix.get_set, hstack, mem])
  | sparse_pos visited update state it eq stack' mem visited' cs state' hn hnext hc ih =>
    rw [captureNextAux_sparse_pos mem hn hnext hc]
    simp at hstack
    exact mem_of_mem_visited (by simp [BitMatrix.get_set, hstack, mem])
  | sparse_neg visited update state it eq stack' mem visited' cs state' hn hnext hc ih =>
    rw [captureNextAux_sparse_neg mem hn hnext hc]
    simp at hstack
    exact mem_of_mem_visited (by simp [BitMatrix.get_set, hstack, mem])
  | sparse_end visited update state it eq stack' mem visited' cs state' hn hnext ih =>
    rw [captureNextAux_sparse_end mem hn hnext]
    simp at hstack
    exact mem_of_mem_visited (by simp [BitMatrix.get_set, hstack, mem])

end Regex.Backtracker.captureNextAux
