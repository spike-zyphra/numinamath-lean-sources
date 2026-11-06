import Mathlib

theorem algebra_322160 (x : ℝ) (hx : x ≠ -1) :
    (13 * x - x ^ 2) / (x + 1) * (x + (13 - x) / (x + 1)) = 42 ↔
    x = 1 ∨ x = 6 ∨ x = 3 + Real.sqrt 2 ∨ x = 3 - Real.sqrt 2 := by
  constructor
  · -- Forward direction: If the equation holds, find the roots
    intro h
    have h1 : x + 1 ≠ 0 := by
      intro h2
      apply hx
      linarith
    have h2 : (13 * x - x ^ 2) / (x + 1) * (x + (13 - x) / (x + 1)) = ((13 * x - x ^ 2) * (x ^ 2 + 13)) / ((x + 1) ^ 2) := by
      have hx1 : x + 1 ≠ 0 := h1
      field_simp [hx1]
      <;> ring
      <;> field_simp [hx1]
      <;> ring
    rw [h2] at h
    have h3 : (13 * x - x ^ 2) * (x ^ 2 + 13) = 42 * ((x + 1) ^ 2) := by
      have hx1 : x + 1 ≠ 0 := h1
      field_simp [hx1] at h ⊢
      nlinarith 
    have h4 : (x - 1) * (x - 6) * (x ^ 2 - 6 * x + 7) = 0 := by 
      nlinarith [sq_pos_of_ne_zero (show x + 1 ≠ 0 by exact h1), sq_nonneg (x^2), sq_nonneg ((x +1)^2), sq_nonneg (x - 3)]
    cases' (mul_eq_zero.mp h4) with h5 h6
    cases' (mul_eq_zero.mp h5) with h7 h8
    · -- Case where x - 1 = 0, so x = 1
      left
      linarith
    · -- Case where x - 6 = 0, so x = 6
      right
      left
      linarith
    · -- Case where x^2 - 6*x + 7 = 0, solving quadratic
      have h7 : x ^ 2 - 6 * x + 7 = 0 := by
        nlinarith 
      have h8 : (x - (3 + Real.sqrt 2)) * (x - (3 - Real.sqrt 2)) = 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      cases' (mul_eq_zero.mp h8) with h9 h10
      · -- Case where x - (3 + Real.sqrt 2) = 0
        right
        right
        left
        linarith
      · -- Case where x - (3 - Real.sqrt 2) = 0
        right
        right
        right
        linarith
  · -- Backward direction: The roots satisfy the equation
    rintro (h | h | h | h)
    · -- Case x = 1
      rw [h]
      norm_num
      <;> linarith 
    · -- Case x = 6
      rw [h]
      norm_num
      <;> linarith 
    · -- Case x = 3 + Real.sqrt 2
      rw [h]
      have hx1 : (3 + Real.sqrt 2 + 1 : ℝ) ≠ 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      field_simp [hx1]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    · -- Case x = 3 - Real.sqrt 2
      rw [h]
      have hx1 : (3 - Real.sqrt 2 + 1 : ℝ) ≠ 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      field_simp [hx1]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]