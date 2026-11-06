import Mathlib

theorem algebra_139989 (a b : ℝ × ℝ) (h₀ : Real.sqrt ((a.1 - b.1)^2 + (a.2 - b.2)^2) = 3)
    (h₁ : Real.sqrt ((a.1 + 2 * b.1)^2 + (a.2 + 2 * b.2)^2) = 6)
    (h₂ : a.1^2 + a.1 * b.1 + a.2^2 + a.2 * b.2 - 2 * (b.1^2 + b.2^2) = -9) :
    Real.sqrt (b.1^2 + b.2^2) = Real.sqrt 7 := by
  have eq1 : (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2 = 9 := by
    calc
      (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2 = (Real.sqrt ((a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2)) ^ 2 := by
        rw [Real.sq_sqrt]
        positivity
      _ = 3 ^ 2 := by
        rw [h₀]
      _ = 9 := by
        norm_num
  have eq2 : (a.1 + 2 * b.1) ^ 2 + (a.2 + 2 * b.2) ^ 2 = 36 := by
    calc
      (a.1 + 2 * b.1) ^ 2 + (a.2 + 2 * b.2) ^ 2 = (Real.sqrt ((a.1 + 2 * b.1) ^ 2 + (a.2 + 2 * b.2) ^ 2)) ^ 2 := by
        rw [Real.sq_sqrt]
        positivity
      _ = 6 ^ 2 := by
        rw [h₁]
      _ = 36 := by
        norm_num
  have eq3 : b.1^2 + b.2^2 = 7 := by
    nlinarith
  -- Now we can compute that $|\boldsymbol{b}| = \sqrt{7}$.
  rw [eq3]
  all_goals linarith