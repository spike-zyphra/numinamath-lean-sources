import Mathlib

theorem inequalities_171079 (x y z : ℝ) (x' y' z' : ℝ) :
    (x * x' + y * y' + z * z') ^ 2 ≤ (x ^ 2 + y ^ 2 + z ^ 2) * (x' ^ 2 + y' ^ 2 + z' ^ 2) := by 
  nlinarith [sq_nonneg (x * y' - y * x'), sq_nonneg (y * z' - z * y'), sq_nonneg (z * x' - x * z')]