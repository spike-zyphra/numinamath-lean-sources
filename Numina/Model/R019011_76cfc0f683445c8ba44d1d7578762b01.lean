import Mathlib

theorem algebra_321350 (x : ℝ) : x = (x^2 + 3 * x - 2)^2 + 3 * (x^2 + 3 * x - 2) - 2 ↔
    x = -1 + Real.sqrt 3 ∨ x = -1 - Real.sqrt 3 ∨ x = -2 + Real.sqrt 2 ∨ x = -2 - Real.sqrt 2 := by
  constructor
  · -- Assume the equation holds, proving the four possible roots
    intro h
    have h1 : (x ^ 2 + 3 * x - 2) ^ 2 + 3 * (x ^ 2 + 3 * x - 2) - 2 - x = 0 := by 
      linarith
    have h2 : (x ^ 2 + 2 * x - 2) * (x ^ 2 + 4 * x + 2) = 0 := by
      nlinarith [sq_nonneg (x ^ 2 + 3 * x - 2), sq_nonneg (x), sq_nonneg (x + 1), sq_nonneg (x + 2)]
    cases' (mul_eq_zero.1 h2) with h3 h4
    · -- First quadratic: x^2 + 2 x - 2 =0
      have h5 : x ^ 2 + 2 * x - 2 = 0 := by linarith
      have h6 : (x - (-1 + Real.sqrt 3)) * (x - (-1 - Real.sqrt 3)) = 0 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
      cases' (mul_eq_zero.1 h6) with h7 h8
      · -- First root
        left
        linarith
      · -- Second root
        right
        left
        linarith
    · -- Second quadratic: x^2 + 4 x + 2 =0
      have h4 : x ^ 2 + 4 * x + 2 = 0 := by linarith
      have h5 : (x - (-2 + Real.sqrt 2)) * (x - (-2 - Real.sqrt 2)) = 0 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
      cases' (mul_eq_zero.1 h5) with h6 h7
      · -- First root
        right 
        right 
        left 
        linarith
      · -- Second root
        right 
        right 
        right 
        linarith
  · -- Assume the four possible roots, proving the equation
    rintro (h | h | h | h)
    · -- First√3 
      rw [h]
      nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    · -- Second√3 
      rw [h]
      nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    · -- First√2 
      rw [h]
      nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
    · -- Second√2 
      rw [h]
      nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]