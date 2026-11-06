import Mathlib

theorem algebra_22449 (z : ℝ) :
    (z^2 - 3 * z + 1)^2 - 3 * (z^2 - 3 * z + 1) + 1 = z ↔
    z = 1 + Real.sqrt 2 ∨ z = 1 - Real.sqrt 2 ∨ z = 2 + Real.sqrt 3 ∨ z = 2 - Real.sqrt 3 := by
  constructor
  · -- Forward direction: equation to roots 
    intro h
    have eq1 : (z^2 - 3 * z + 1)^2 - 3 * (z^2 - 3 * z + 1) + 1 - z = 0 := by linarith
    have h2 : (z - 1 - Real.sqrt 2) * (z - 1 + Real.sqrt 2) * (z - 2 - Real.sqrt 3) * (z - 2 + Real.sqrt 3) = 0 := by 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num),
          sq_nonneg (z ^ 2 - 2 * z - 1), sq_nonneg (z ^ 2 - 4 * z + 1)]
    cases' (mul_eq_zero.1 h2) with h3 h4
    cases' (mul_eq_zero.1 h3) with h5 h6
    cases' (mul_eq_zero.1 h5) with h7 h8
    · -- Case z - 1 - Real.sqrt 2 = 0 
      have hz : z = 1 + Real.sqrt 2 := by
        linarith 
      left 
      exact hz
    · -- Case z - 1 + Real.sqrt 2 = 0 
      have hz : z = 1 - Real.sqrt 2 := by 
        linarith 
      right 
      left 
      exact hz
    · -- Case z - 2 - Real.sqrt 3 = 0 
      have hz : z = 2 + Real.sqrt 3 := by 
        linarith 
      right 
      right 
      left 
      exact hz
    · -- Case z - 2 + Real.sqrt 3 = 0 
      have hz : z = 2 - Real.sqrt 3 := by 
        linarith 
      right 
      right 
      right 
      exact hz
  · -- Backward direction: roots to equation 
    rintro (h | h | h | h)
    · -- Case z = 1 + Real.sqrt 2 
      rw [h] 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    · -- Case z = 1 - Real.sqrt 2 
      rw [h] 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    · -- Case z = 2 + Real.sqrt 3 
      rw [h] 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    · -- Case z = 2 - Real.sqrt 3 
      rw [h] 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]