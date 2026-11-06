import Mathlib

theorem algebra_203167 (a : ℕ → ℝ) (ha : a 0 = 60) (ha' : a 1 = 80)
    (h : ∀ i ∈ Finset.range 49, a (i + 1) = (∑ j ∈ Finset.range (i + 1), a j) / (i + 1)) :
    a 41 = 70 ∧ a 49 = 70 := by 
  have h0 := h 0 (by norm_num [Finset.mem_range])
  norm_num [Finset.sum_range_succ, ha] at h0 
  all_goals 
    norm_num [ha'] at h0 ⊢
    <;> try linarith 
    <;> try tauto