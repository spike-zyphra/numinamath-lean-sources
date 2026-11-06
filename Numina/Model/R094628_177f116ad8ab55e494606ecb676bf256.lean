import Mathlib

theorem algebra_256511 (x : ℝ) (hx : 2 * (x - 3 * Real.sqrt 5) * (x - 5 * Real.sqrt 3) = 0) :
    min (3 * Real.sqrt 5) x = 3 * Real.sqrt 5 := by
  cases' (mul_eq_zero.mp hx) with h1 h2
  · -- Case where 2 * (x - 3 * sqrt 5) = 0
    have h3 : x - 3 * Real.sqrt 5 = 0 := by
      linarith
    have hx_eq : x = 3 * Real.sqrt 5 := by
      linarith
    rw [hx_eq]
    simp
  · -- Case where (x - 5 * sqrt 3) = 0
    have hx_eq : x = 5 * Real.sqrt 3 := by
      linarith
    rw [hx_eq]
    have h5 : 3 * Real.sqrt 5 ≤ 5 * Real.sqrt 3 := by
      have h1 : (3 * Real.sqrt 5) ^ 2 ≤ (5 * Real.sqrt 3) ^ 2 := by
        have h11 : (3 * Real.sqrt 5) ^ 2 = 45 := by
          calc
            (3 * Real.sqrt 5) ^ 2 = 9 * (Real.sqrt 5 * Real.sqrt 5) := by ring
            _ = 9 * (Real.sqrt 5) ^ 2 := by ring
            _ = 9 * 5 := by rw [Real.sq_sqrt]; positivity
            _ = 45 := by norm_num
        have h22 : (5 * Real.sqrt 3) ^ 2 = 75 := by
          calc
            (5 * Real.sqrt 3) ^ 2 = 25 * (Real.sqrt 3 * Real.sqrt 3) := by ring
            _ = 25 * (Real.sqrt 3) ^ 2 := by ring
            _ = 25 * 3 := by rw [Real.sq_sqrt]; positivity
            _ = 75 := by norm_num
        nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 3]
      nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    have h6 : min (3 * Real.sqrt 5) (5 * Real.sqrt 3) = 3 * Real.sqrt 5 := by
      apply min_eq_left
      linarith [h5]
    linarith [h6]