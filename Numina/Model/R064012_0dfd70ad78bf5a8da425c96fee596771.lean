import Mathlib

theorem calculus_22923 (x y z : ℝ) (h : x^2 + 2*x + y^2 + 6*y + z^2 - 12*z + 30 = 0) :
    Real.sqrt ((x+1)^2 + (y+3)^2 + (z-6)^2) = 4 := by
  have h1 : (x + 1) ^ 2 + (y + 3) ^ 2 + (z - 6) ^ 2 = 16 := by
    nlinarith [sq_nonneg (x + 1), sq_nonneg (y + 3), sq_nonneg (z - 6)]
  rw [h1]
  exact Real.sqrt_eq_cases.2 (Or.inl (by norm_num))