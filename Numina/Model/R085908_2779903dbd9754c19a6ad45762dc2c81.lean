import Mathlib

theorem algebra_322995 (x : ℝ) (hx : x ≠ -1) :
    (13 * x - x ^ 2) / (x + 1) * (x + (13 - x) / (x + 1)) = 42 ↔
    x = 1 ∨ x = 6 ∨ x = 3 + Real.sqrt 2 ∨ x = 3 - Real.sqrt 2 := by
  constructor
  · -- Forward direction: assume left, prove right
    intro h
    have h1 : (x + 1) ≠ 0 := by
      intro h2
      apply hx
      linarith
    have eq1 : (13 * x - x ^ 2) / (x + 1) * (x + (13 - x) / (x + 1)) = ( (13 * x - x^2) * (x ^ 2 + 13) ) / (x + 1) ^ 2 := by
      have h1' : (x + 1) ≠ 0 := h1
      field_simp
      <;> ring_nf
      <;> field_simp
      <;> ring
    rw [eq1] at h
    have eq2 : (13 * x - x^2) * (x^2 + 13) = 42 * (x + 1) ^ 2 := by
      field_simp [h1] at h ⊢
      nlinarith [sq_nonneg (x + 1), sq_nonneg (13 * x - x^2 - 42 * (x + 1)), sq_nonneg ((x ^ 2 + 13) - 42 * (x + 1)), sq_nonneg (x ^ 2 - 42), sq_nonneg (x - 1), sq_nonneg (x - 6), sq_nonneg (x ^ 2 - 6 * x +7)]
    have h2 : (x - 1) * (x - 6) * (x ^ 2 - 6 * x + 7) = 0 := by
      nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x - 6), sq_nonneg (x^2 - 6*x +7), sq_nonneg (x ^ 2 - 42), sq_nonneg (13 * x - x^2 - 42 * (x + 1)), sq_nonneg ((x^2 + 13) - 42 * (x + 1)), sq_nonneg (x - 3), sq_nonneg (x * (x - 3)), sq_nonneg ((x - 3)^2)]
    cases' (mul_eq_zero.mp h2) with h3 h4
    cases' (mul_eq_zero.mp h3) with h5 h6
    · -- Case that $x = 1$
      left
      linarith
    · -- Case that $x = 6$
      right
      left
      linarith
    · -- Case that $x^2 - 6x +7 = 0$
      have h7 : x ^ 2 - 6 * x + 7 = 0 := by
        linarith
      have h8 : (x - (3 + Real.sqrt 2)) * (x - (3 - Real.sqrt 2)) = 0 := by
        nlinarith [sq_nonneg (x - 3), sq_nonneg (x * (x - 3)), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      cases' (mul_eq_zero.mp h8) with h9 h10
      · -- Case that $x = 3 + √2$
        right
        right
        left
        linarith
      · -- Case that $x = 3 - √2$
        right
        right
        right
        linarith
  · -- Backward direction: assume right, prove left
    rintro (h | h | h | h)
    · -- Case x = 1
      rw [h]
      norm_num
    · -- Case x = 6
      rw [h]
      norm_num
    · -- Case x = 3 + √2
      rw [h]
      field_simp [show 3 + Real.sqrt 2 + 1 ≠ 0 by nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]]
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2)]
    · -- Case x = 3 - √2
      rw [h]
      field_simp [show 3 - Real.sqrt 2 + 1 ≠ 0 by nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]]
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (Real.sqrt 2)]