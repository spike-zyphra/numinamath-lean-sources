import Mathlib

theorem algebra_93236 (x : ℝ) (hx : 5 * abs x + 8 ≥ 0) :
    Real.sqrt (5 * abs x + 8) = Real.sqrt (x ^ 2 - 16) ↔ x = -8 ∨ x = 8 := by
  constructor
  · -- Assume Real.sqrt (5 * abs x + 8) = Real.sqrt (x ^ 2 - 16), prove x = -8 ∨ x = 8
    intro h_eq
    have h1 : x ^ 2 - 16 ≥ 0 := by
      by_contra h
      push_neg at h
      have h2 : Real.sqrt (x ^ 2 - 16) = 0 := by
        rw [Real.sqrt_eq_zero'.mpr]
        linarith
      have h3 : Real.sqrt (5 * abs x + 8) = 0 := by
        linarith [h_eq, h2]
      have h4 : 5 * abs x + 8 = 0 := by
        calc
          5 * abs x + 8 = (Real.sqrt (5 * abs x + 8)) ^ 2 := by 
            rw [Real.sq_sqrt]
            linarith
          _ = (0) ^ 2 := by 
            rw [h3]
          _ = (0 : ℝ) := by norm_num
      have h5 : abs x ≥ 0 := abs_nonneg x
      nlinarith [abs_nonneg x]
    have h_eq1 : 5 * abs x + 8 = x ^ 2 - 16 := by 
      calc
        5 * abs x + 8 = (Real.sqrt (5 * abs x + 8)) ^ 2 := by
          rw [Real.sq_sqrt]
          linarith
        _ = (Real.sqrt (x ^ 2 - 16)) ^ 2 := by 
          rw [h_eq]
        _ = x ^ 2 - 16 := by 
          rw [Real.sq_sqrt]
          linarith
    by_cases h2 : x ≥ 0
    · -- x ≥ 0
      have h3 : abs x = x := abs_of_nonneg h2
      rw [h3] at h_eq1
      have h4 : x ^ 2 - 5 * x - 24 = 0 := by
        linarith
      have : (x - 8) * (x + 3) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp this) with h5 h6
      · -- x - 8 = 0
        right
        linarith
      · -- x + 3 = 0
        nlinarith
    · -- x < 0
      have h2 : x < 0 := by
        by_contra h
        push_neg at h
        have : x ≥ 0 := by 
          linarith
        contradiction
      have h3 : abs x = -x := by
        rw [abs_of_neg h2]
      rw [h3] at h_eq1
      have h4 : x ^ 2 + 5 * x - 24 = 0 := by 
        linarith
      have : (x + 8) * (x - 3) = 0 := by 
        nlinarith
      cases' (mul_eq_zero.mp this) with h5 h6
      · -- x + 8 = 0
        left
        linarith
      · -- x - 3 = 0
        nlinarith
  · -- Assume x = -8 ∨ x = 8, prove Real.sqrt (5 * abs x + 8) = Real.sqrt (x ^ 2 - 16)
    rintro (h_eq | h_eq)
    · -- x = -8
      rw [h_eq]
      have h1 : abs (-8 : ℝ) = 8 := by 
        norm_num [abs]
      rw [h1]
      have h2 : (-8 : ℝ) ^ 2 - 16 = 48 := by 
        norm_num
      rw [h2]
      all_goals norm_num [Real.sqrt_eq_iff_sq_eq]
    · -- x = 8
      rw [h_eq]
      have h1 : abs (8 : ℝ) = 8 := by 
        norm_num [abs]
      rw [h1]
      have h2 : (8 : ℝ) ^ 2 - 16 = 48 := by 
        norm_num
      rw [h2]
      all_goals norm_num [Real.sqrt_eq_iff_sq_eq]