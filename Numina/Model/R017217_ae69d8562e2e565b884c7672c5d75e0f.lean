import Mathlib

theorem algebra_3887 (x : ℝ) : Real.sqrt (2 * (x^4 + 4)) = 3 * x^2 - 10 * x + 6 ↔
    x = 3 - Real.sqrt 7 ∨ x = 3 + Real.sqrt 7 := by
  constructor
  · -- Assume the left side holds, prove the right side
    intro h
    have h1 : 0 ≤ 3 * x^2 - 10 * x + 6 := by
      by_contra h2
      push_neg at h2
      have h3 : Real.sqrt (2 * (x^4 + 4)) ≥ 0 := Real.sqrt_nonneg (2 * (x ^ 4 + 4))
      have h4 : 3 * x^2 - 10 * x + 6 < 0 := by linarith
      nlinarith [h, h3, h4, sq_nonneg (x^2 - 3), sq_nonneg (x - 3), 
          Real.sqrt_nonneg (2 * (x ^ 4 + 4)), Real.sq_sqrt (show 0 ≤ (2 * (x ^4 + 4)) by positivity)]
    have h2 : (Real.sqrt (2 * (x ^ 4 + 4))) ^ 2 = (3 * x ^ 2 - 10 * x + 6) ^ 2 := by
      rw [h]
    have h3 : (Real.sqrt (2 * (x ^4 + 4))) ^ 2 = 2 * (x ^4 + 4) := by 
      exact Real.sq_sqrt (by positivity)
    have h4 : 2 * (x ^4 + 4) = (3 * x ^ 2 - 10 * x + 6) ^ 2 := by
      linarith [h2, h3]
    have h4 : (x - (3 - Real.sqrt 7)) * (x - (3 + Real.sqrt 7)) = 0 := by
      nlinarith [sq_nonneg (x^2 - 3), sq_nonneg (x - 3), 
          sq_nonneg (x^2 - (3 - Real.sqrt 7)^2), sq_nonneg (x - (3 - Real.sqrt 7)), sq_nonneg (x - (3 + Real.sqrt 7)), 
          Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]
    cases' (mul_eq_zero.1 h4) with h5 h6
    · -- x - (3 - Real.sqrt 7) = 0
      left
      linarith
    · -- x - (3 + Real.sqrt 7) = 0 
      right
      linarith
  · -- Assume the right side holds, prove the left side
    rintro (h | h)
    · -- x = 3 - Real.sqrt 7 
      rw [h]
      have h24 : 2 * ((3 - Real.sqrt 7 : ℝ) ^ 4 + 4) = (3 * (3 - Real.sqrt 7) ^ 2 - 10 * (3 - Real.sqrt 7) + 6) ^ 2 := by
        nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), 
            sq_nonneg (Real.sqrt 7 ^ 2)]
      have h25 : 0 ≤ (3 * (3 - Real.sqrt 7) ^ 2 - 10 * (3 - Real.sqrt 7) + 6 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), sq_nonneg (Real.sqrt 7 ^ 2)]
      have h11 : Real.sqrt (2 * ((3 - Real.sqrt 7 : ℝ) ^ 4 + 4)) = 3 * (3 - Real.sqrt 7 : ℝ) ^ 2 - 10 * (3 - Real.sqrt 7 : ℝ) + 6 := by
        rw [show 2 * ((3 - Real.sqrt 7 : ℝ) ^ 4 + 4) = (3 * (3 - Real.sqrt 7 : ℝ) ^ 2 - 10 * (3 - Real.sqrt 7 : ℝ) + 6) ^ 2 by linarith]
        rw [Real.sqrt_sq (show 0 ≤ (3 * (3 - Real.sqrt 7 : ℝ) ^ 2 - 10 * (3 - Real.sqrt 7 : ℝ) + 6 : ℝ) by linarith)]
      linarith [h11, Real.sqrt_nonneg (2 * ((3 - Real.sqrt 7 : ℝ) ^4 + 4)), h25]
    · -- x = 3 + Real.sqrt 7 
      rw [h]
      have h34 : 2 * ((3 + Real.sqrt 7 : ℝ) ^ 4 + 4) = (3 * (3 + Real.sqrt 7) ^ 2 - 10 * (3 + Real.sqrt 7) + 6) ^ 2 := by
        nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), 
            sq_nonneg (Real.sqrt 7 ^ 2)]
      have h41 : 0 ≤ (3 * (3 + Real.sqrt 7) ^ 2 - 10 * (3 + Real.sqrt 7) + 6 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), sq_nonneg (Real.sqrt 7 ^ 2)]
      have h32 : Real.sqrt (2 * ((3 + Real.sqrt 7 : ℝ) ^ 4 + 4)) = 3 * (3 + Real.sqrt 7 : ℝ) ^ 2 - 10 * (3 + Real.sqrt 7 : ℝ) + 6 := by
        rw [show 2 * ((3 + Real.sqrt 7 : ℝ) ^ 4 + 4) = (3 * (3 + Real.sqrt 7) ^ 2 - 10 * (3 + Real.sqrt 7) + 6) ^ 2 by linarith]
        rw [Real.sqrt_sq (show 0 ≤ (3 * (3 + Real.sqrt 7 : ℝ) ^ 2 - 10 * (3 + Real.sqrt 7 : ℝ) + 6 : ℝ) by linarith)]
      linarith [h32, Real.sqrt_nonneg (2 * ((3 + Real.sqrt 7 : ℝ) ^4 + 4)), h41]