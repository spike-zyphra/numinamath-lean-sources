import Mathlib

theorem algebra_196917 {f : ℝ → ℝ} (hf : ∀ x, f x = (x ^ 2 + x - 2) ^ 2002 + 3)
    (P : ℝ) (hP : f (Real.sqrt 5 / 2 - 1 / 2) = P) :
    P = 4 := by
  have eq1 : f (Real.sqrt 5 / 2 - 1 / 2) = 4 := by
    rw [hf]
    have h_eq : (Real.sqrt 5 / 2 - 1 / 2 : ℝ) ^ 2 + (Real.sqrt 5 / 2 - 1 / 2 : ℝ) - 2 = -1 := by
      nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), sq_nonneg (Real.sqrt 5 - 1)]
    rw [h_eq]
    norm_num
  linarith [hP, eq1]