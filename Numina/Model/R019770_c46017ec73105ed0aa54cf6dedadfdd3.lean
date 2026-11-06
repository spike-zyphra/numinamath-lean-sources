import Mathlib

open Real

set_option maxHeartbeats 800000 in
theorem algebra_11700 {a : ℝ} (ha : a ≠ 0 ∧ a ≠ 1) (h : ∀ n, ∑ i in Finset.range n, a ^ i = a / (1 - a) * (1 - a ^ n))
    (b : ℕ → ℝ) (hb : ∀ n, b n = a ^ n * log (abs (a ^ n))) :
    (∃ m, ∀ n, b n ≥ b m) ↔ m = 8 := by
  have h1 := h 1
  norm_num [Finset.sum_range_succ] at h1
  -- Now, we have 1 = a
  have h1 : (1 : ℝ) = a := by
    have hne : 1 - a ≠ 0 := by
      intro h'
      apply ha.2
      linarith
    field_simp [hne] at h1
    linarith
  have h4 : a = 1 := by linarith
  exfalso
  exact ha.2 h4