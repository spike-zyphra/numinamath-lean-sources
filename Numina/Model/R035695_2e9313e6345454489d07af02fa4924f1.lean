import Mathlib

theorem algebra_172724 {a : ℝ} (ha : a ≠ 0) (h : 1 / a + abs a + 1 = 0) : a = (1 - Real.sqrt 5) / 2 := by
  by_cases h1 : a ≥ 0
  · -- Assume a ≥ 0, then abs a = a
    have h2 : abs a = a := abs_of_nonneg h1
    rw [h2] at h
    have h3 : a ≠ 0 := ha
    have eq1 : a ^ 2 + a + 1 = 0 := by
      field_simp [h3] at h
      nlinarith
    have eq2 : a ^ 2 + a + 1 > 0 := by
      nlinarith [sq_pos_of_pos (show (0 : ℝ) < 2 by norm_num), sq_nonneg (a + 1 / 2)]
    linarith
  · -- Assume a < 0, then abs a = -a
    have h2 : abs a = -a := abs_of_neg (lt_of_not_ge h1)
    rw [h2] at h
    have h3 : a < 0 := by linarith
    have h4 : a ≠ 0 := ha
    have h5 : a ^ 2 - a - 1 = 0 := by
      field_simp [h4] at h
      nlinarith [h3]
    have h7 : a = (1 + Real.sqrt 5) / 2 ∨ a = (1 - Real.sqrt 5) / 2 := by
      have h8 : a ^ 2 - a - 1 = 0 := h5
      have h12 : a ^ 2 - a - 1 = (a - (1 + Real.sqrt 5) / 2) * (a - (1 - Real.sqrt 5) / 2) := by
        nlinarith [Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
      rw [h12] at h8
      cases' mul_eq_zero.1 h8 with h13 h14
      · -- a - (1 + Real.sqrt 5) / 2 = 0
        left
        linarith
      · -- a - (1 - Real.sqrt 5) / 2 = 0
        right
        linarith
    cases h7 with
    | inl h8 =>
      -- In this case, $a > 0$ which contradicts $a < 0$
      have h9 : a > 0 := by
        nlinarith [Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
      linarith
    | inr h8 =>
      linarith