import Mathlib

theorem algebra_234306 (x : ℝ) :
    (x - abs x)^2 + 2020 * (x + abs x) = 2020 ↔ x = 0.5 ∨ x = -Real.sqrt 505 := by
  constructor
  · -- Forward implication: If the equation holds, then x = 0.5 or x = -sqrt(505)
    intro h
    by_cases h1 : x ≥ 0
    · -- If x ≥ 0, then |x| = x
      have h2 : abs x = x := abs_of_nonneg h1
      rw [h2] at h
      have h3 : x = 0.5 := by
        nlinarith
      left
      exact h3
    · -- Case x < 0
      have h2 : abs x = -x := abs_of_neg (lt_of_not_ge h1)
      rw [h2] at h
      have h4 : x ^ 2 = 505 := by
        nlinarith
      have h4' : x < 0 := by linarith
      have h5 : x = - Real.sqrt 505 := by
        have h6 : x^2 - 505 = 0 := by
          nlinarith
        have h7 : (x - Real.sqrt 505) * (x + Real.sqrt 505) = 0 := by
          nlinarith [Real.sqrt_nonneg 505, Real.sq_sqrt (show (505 : ℝ) ≥ 0 by norm_num : (505 : ℝ) ≥ 0)]
        cases' (mul_eq_zero.1 h7) with h8 h9
        · -- Case x = sqrt 505, which is positive, contradicting x < 0
          have h11 : Real.sqrt 505 ≥ 0 := Real.sqrt_nonneg 505
          nlinarith [Real.sq_sqrt (show (505 : ℝ) ≥ 0 by norm_num : (505 : ℝ) ≥ 0)]
        · -- Case x = -sqrt 505
          nlinarith [Real.sqrt_nonneg 505]
      right
      exact h5
  · -- Backward direction: If x = 0.5 or x = -sqrt(505), then the equation holds
    rintro (h | h)
    · -- Case x = 0.5
      rw [h]
      norm_num [abs_of_nonneg]
    · -- Case x = -sqrt 505
      rw [h]
      have h1 : Real.sqrt 505 ≥ 0 := Real.sqrt_nonneg 505
      have h2 : abs (-Real.sqrt 505 : ℝ) = Real.sqrt 505 := by
        rw [abs_neg]
        simp [Real.sqrt_nonneg]
      rw [h2]
      nlinarith [Real.sq_sqrt (show (505 : ℝ) ≥ 0 by norm_num : (505 : ℝ) ≥ 0), Real.sqrt_nonneg 505]