import Mathlib

theorem algebra_242966 (a b : ℝ × ℝ) (h : Real.sqrt ((a.1 + b.1)^2 + (a.2 + b.2)^2) = 3) :
    a.1 * b.1 + a.2 * b.2 ≤ 9 / 4 := by
  have h1 : (a.1 + b.1) ^ 2 + (a.2 + b.2) ^ 2 = 9 := by
    calc
      (a.1 + b.1) ^ 2 + (a.2 + b.2) ^ 2 = (Real.sqrt ((a.1 + b.1) ^ 2 + (a.2 + b.2) ^ 2)) ^ 2 := by
        rw [Real.sq_sqrt]
        positivity
      _ = 3 ^ 2 := by rw [h]
      _ = (9 : ℝ) := by norm_num

  nlinarith [sq_nonneg (a.1 - b.1), sq_nonneg (a.2 - b.2),
    sq_nonneg (a.1 + b.1), sq_nonneg (a.2 + b.2),
    Real.sqrt_nonneg ((a.1 + b.1) ^ 2 + (a.2 + b.2) ^ 2)]