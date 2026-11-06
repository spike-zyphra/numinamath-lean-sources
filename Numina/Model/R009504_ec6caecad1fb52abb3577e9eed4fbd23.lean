import Mathlib

theorem number_theory_275729 (a : ℝ) : ∃ x y z, x^2 + y^2 + z^2 = 3 * a^4 + 1 := by 
  use Real.sqrt 3 * a^2
  use 1
  use (0 : ℝ)
  -- Calculate cases
  have h1 : ((Real.sqrt 3 * a^2) : ℝ)^2 = 3 * a^4 := by
    calc
      ((Real.sqrt 3 * a^2) : ℝ)^2 = (Real.sqrt 3)^2 * (a^2) ^ 2 := by
        ring_nf
      _ = 3 * (a^2) ^ 2 := by
        rw [Real.sq_sqrt]
        all_goals linarith
        all_goals nlinarith
      _ = 3 * a^4 := by
        ring_nf
  nlinarith [Real.sqrt_nonneg 3, sq_nonneg (a^2), sq_nonneg (a), sq_nonneg (a * a), h1]