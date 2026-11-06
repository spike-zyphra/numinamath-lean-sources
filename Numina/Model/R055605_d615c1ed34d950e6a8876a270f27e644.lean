import Mathlib

open Real

theorem algebra_293804 {f : ℕ → ℝ} (hf : ∀ x, f x = 1 / (x ^ 3 + 3 * x ^ 2 + 2 * x)) :
    IsLeast {n | 0 < n ∧ ∑ i in Finset.Icc 1 n, f i > 503 / 2014} 44 := by
  constructor
  · -- Show 44 is in the set
    constructor
    · norm_num
    · -- Show that the sum is greater than 503/2014
      norm_num [Finset.sum_Icc_succ_top, hf] -- Compute sum explicitly
      <;> linarith
  · -- Show 44 is the smallest
    intro n hn
    have ⟨hn_pos, hn_sum⟩ := hn
    by_contra h
    push_neg at h
    have h' : n ≤ 43 := by omega
    interval_cases n <;> norm_num [Finset.sum_Icc_succ_top, hf] at hn_sum ⊢ <;> all_goals linarith