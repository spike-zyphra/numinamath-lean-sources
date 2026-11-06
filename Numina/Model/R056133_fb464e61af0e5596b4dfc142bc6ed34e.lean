import Mathlib

theorem algebra_234272 (x : ℝ) :
    (x - abs x) ^ 2 + x + abs x = 2020 ↔ x = 1010 ∨ x = -Real.sqrt 505 := by
  constructor
  · -- Assume $(x - abs x) ^ 2 + x + abs x = 2020$, prove $x = 1010 ∨ x = -Real.sqrt 505$
    rintro h
    by_cases h1 : x ≥ 0
    · -- If x ≥ 0, then abs x = x
      rw [abs_of_nonneg h1] at h
      have h2 : x = 1010 := by
        nlinarith
      left
      exact h2
    · -- Case x < 0
      rw [abs_of_neg (lt_of_not_ge h1)] at h
      have h2 : x^2 = 505 := by
        nlinarith
      have h3 : x < 0 := by linarith
      have h4 : x = -Real.sqrt 505 := by
        have h5 : Real.sqrt 505 ^ 2 = 505 := Real.sq_sqrt (by norm_num)
        have h6 : x^2 - Real.sqrt 505 ^ 2 = 0 := by linarith [h2, h5]
        have h7 : (x - Real.sqrt 505) * (x + Real.sqrt 505) = 0 := by
          nlinarith [h6]
        cases' (mul_eq_zero.1 h7) with h8 h9
        · -- Case x - Real.sqrt 505 = 0, so x = Real.sqrt 505
          have h10 : x = Real.sqrt 505 := by linarith
          have h11 : x ≥ 0 := by linarith [Real.sqrt_nonneg 505, h10]
          linarith [h1, h11]
        · -- Case x + Real.sqrt 505 = 0, so x = -Real.sqrt 505
          have h12 : x = -Real.sqrt 505 := by linarith
          exact h12
      right
      exact h4
  · -- Assume x = 1010 or x = -Real.sqrt 505, prove (x - abs x) ^ 2 + x + abs x = 2020
    rintro (h | h)
    · -- Case x = 1010
      rw [h]
      norm_num [abs_of_nonneg]
    · -- Case x = -Real.sqrt 505
      rw [h]
      have h1 : Real.sqrt 505 ≥ 0 := Real.sqrt_nonneg 505
      have h2 : Real.sqrt 505 > 0 := by positivity
      have h3 : abs (-Real.sqrt 505 : ℝ) = Real.sqrt 505 := by
        rw [abs_neg]
        rw [abs_of_nonneg h1]
      rw [h3]
      nlinarith [Real.sq_sqrt (show 505 ≥ 0 by norm_num)]