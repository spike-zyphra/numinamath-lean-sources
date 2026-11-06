import Mathlib

theorem algebra_2704 {a : ℝ} (h : a ≠ 0) (h1 : a + 1 / a = 4 / 3 * Real.sqrt 3) :
    a ^ 5 + 1 / a ^ 3 = 82 / 9 * Real.sqrt 3 ∨ a ^ 5 + 1 / a ^ 3 = 82 / 27 * Real.sqrt 3 := by
  have eq1 : a^2 + 1 = 4 / 3 * Real.sqrt 3 * a := by
    have h2 : a ≠ 0 := h
    field_simp at h1 ⊢
    linarith
  have eq2 : (a - Real.sqrt 3) * (a - Real.sqrt 3 / 3) = 0 := by
    nlinarith [Real.sqrt_pos.mpr (by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ (3 : ℝ)), sq_nonneg (a - Real.sqrt 3), sq_nonneg (a - Real.sqrt 3 / 3), Real.sqrt_nonneg 3]
  have h2 : a = Real.sqrt 3 ∨ a = Real.sqrt 3 / 3 := by
    cases (mul_eq_zero.mp eq2) with
    | inl h3 =>
      left
      linarith
    | inr h4 =>
      right
      linarith
  cases h2 with
  | inl ha1 =>
    -- Assume a = Real.sqrt 3, compute a ^ 5 + 1 / a ^ 3
    have ha1' : a = Real.sqrt 3 := ha1
    have h3 : a^5 + 1 / a^3 = 82 / 9 * Real.sqrt 3 := by
      rw [ha1']
      have h4 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      have h5 : (Real.sqrt 3 : ℝ) ^ 4 = 9 := by
        calc
          (Real.sqrt 3 : ℝ) ^ 4 = ((Real.sqrt 3 : ℝ) ^ 2) ^ 2 := by ring
          _ = 3 ^ 2 := by rw [h4]
          _ = 9 := by norm_num
      field_simp [(show (Real.sqrt 3 : ℝ) ≠ 0 by positivity), h4]
      nlinarith [h4, h5, Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
    left
    linarith [h3]
  | inr ha2 =>
    -- Assume a = Real.sqrt 3 / 3, compute a ^ 5 + 1 / a ^ 3
    have ha2' : a = Real.sqrt 3 / 3 := by
      linarith
    have h6 : a^5 + 1 / a^3 = 82 / 27 * Real.sqrt 3 := by
      rw [ha2']
      have h4 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      have h5 : (Real.sqrt 3 : ℝ) ^ 4 = 9 := by
        calc
          (Real.sqrt 3 : ℝ) ^ 4 = ((Real.sqrt 3 : ℝ) ^ 2) ^ 2 := by ring
          _ = 3 ^ 2 := by rw [h4]
          _ = 9 := by norm_num
      field_simp [(show (Real.sqrt 3 : ℝ) ≠ 0 by positivity), h4]
      nlinarith [h4, h5, Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
    right
    linarith [h6]