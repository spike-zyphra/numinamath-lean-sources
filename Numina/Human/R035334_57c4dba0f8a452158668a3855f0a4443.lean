import Mathlib

/-  Let $x,y,z$ be positive real numbers such that  $x^2+y^2+z^2=3$. Prove that
\[ xyz(x+y+z)+2021\geqslant 2024xyz\] -/
theorem inequalities_45118 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x ^ 2 + y ^ 2 + z ^ 2 = 3) :
    x * y * z * (x + y + z) + 2021 ≥ 2024 * x * y * z := by 
  nlinarith [sq_nonneg (x + y + z), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
    sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]