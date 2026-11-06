import Mathlib

theorem algebra_193935 {a : ℕ → ℝ} (ha : a 1 > 2)
    (h1 : a 1 = a 0) (h2 : ∀ n, a (n + 1) = (a n)^2 / (2 * (a n - 1))) :
    ∀ n, ∑ i in Finset.Icc 1 n, a i < 2 * n + 2 * a 0 - 6 + 4 / a 0 := by
  have h3 := h2 0
  rw [h1] at h3
  have h4 : a 0 = (a 0) ^ 2 / (2 * (a 0 - 1)) := by
    linarith
  have h5 : a 0 > 2 := by
    linarith [ha, h1]
  have h6 : a 0 - 1 ≠ 0 := by
    linarith
  have eq3 : a 0 * 2 * (a 0 - 1) = (a 0) ^ 2 := by
    have h9 : a 0 = (a 0) ^ 2 / (2 * (a 0 - 1)) := by linarith [h4]
    have h10 : 2 * (a 0 - 1) ≠ 0 := by
      apply mul_ne_zero
      norm_num
      all_goals linarith [h5]
    field_simp [h10] at h9 ⊢
    nlinarith [sq_pos_of_pos (show (0 : ℝ) < a 0 - 2 by linarith [h5]), sq_nonneg (a 0 - 2)]
  have h8 : a 0 * (a 0 - 2) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h8) with h9 h10
  · -- Case where a 0 = 0
    linarith
  · -- Case where a 0 - 2 = 0
    have h11 : a 0 = 2 := by linarith
    linarith [h5, h11]