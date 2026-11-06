import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_166606 (f : ℝ → ℝ → ℝ)
  (h₀ : ∀ x y, f x y = x^2 + y^2 - 4 * y)
  (h₁ : ∀ x y, abs (4 * x - 3 * y) + 5 * sqrt (x^2 + y^2 - 20 * y + 100) = 30) :
  IsLeast {z | ∃ x y, z = f x y ∧ abs (4 * x - 3 * y) + 5 * sqrt (x^2 + y^2 - 20 * y + 100) = 30} 4.76 := by

  have h2 := h₁ 0 0
  -- Compute left side
  -- abs (4 * 0 - 3 * 0) +5 * sqrt (0^2 +0^2 -20*0 +100)
  -- abs (0) +5 * sqrt (0 +0 -0 +100)
  -- abs 0 +5 * sqrt 100
  -- 0 +5 *10= 0 +50=50.
  -- But h₁ 0 0 says that it's 30. Therefore, 50=30, which is false. Therefore h₁ is false.
  have h3 : abs (4 * (0 : ℝ) - 3 * (0 : ℝ)) + 5 * sqrt ((0 : ℝ) ^ 2 + (0 : ℝ) ^ 2 - 20 * (0 : ℝ) + 100) = 30 := by
    simpa using h2
  -- compute that left side is 50
  -- compute that 50 ≠ 30
  have h4 : abs (4 * (0 : ℝ) - 3 * (0 : ℝ)) + 5 * sqrt ((0 : ℝ) ^ 2 + (0 : ℝ) ^ 2 - 20 * (0 : ℝ) + 100) = 50 := by
    have h5 : sqrt ((0 : ℝ) ^ 2 + (0 : ℝ) ^ 2 - 20 * (0 : ℝ) + 100) = 10 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h5]
    norm_num [abs]
    all_goals norm_num
    all_goals norm_num
  -- contradiction 50 = 30
  linarith [h3, h4]