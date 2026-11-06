import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_56009 :
  IsLeast {x * (x + 4) * (x + 8) * (x + 12) | x : ℝ} (-256) := by
  constructor
  · -- Show that -256 is achievable
    use -6 + 2 * Real.sqrt 5
    have h1 : Real.sqrt 5 ^ 2 = 5 := by
      rw [Real.sq_sqrt]
      all_goals norm_num
    have h2 : (-6 + 2 * Real.sqrt 5) * ((-6 + 2 * Real.sqrt 5) + 4) * ((-6 + 2 * Real.sqrt 5) + 8) * ((-6 + 2 * Real.sqrt 5) + 12) = -256 := by
      nlinarith [Real.sqrt_nonneg 5, h1, sq_nonneg (Real.sqrt 5 - 2), sq_nonneg (Real.sqrt 5 + 2)]
    linarith
  · -- Show that -256 is a lower bound
    intro y
    rintro ⟨x, hx⟩
    have h3 : x * (x + 4) * (x + 8) * (x + 12) ≥ -256 := by
      nlinarith [sq_nonneg (x^2 + 12 * x + 24), sq_nonneg (x + 6 - 2 * Real.sqrt 5), sq_nonneg (x + 6 + 2 * Real.sqrt 5), Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num : (0 : ℝ) ≤ 5)]
    linarith [h3, hx]