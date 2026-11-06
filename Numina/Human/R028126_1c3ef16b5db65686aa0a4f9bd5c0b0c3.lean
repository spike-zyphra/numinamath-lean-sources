import Mathlib

/- $3 \cdot 43$ If $x=\left(1+\frac{1}{n}\right)^{n}, y=\left(1+\frac{1}{n}\right)^{n+1}$, prove: $y^{x}=x^{y}$.
(6th Canadian Mathematical Olympiad, 1974) -/
theorem algebra_111132 {n : ℕ} (hn : n ≠ 0) (x y : ℝ)
    (hx : x = (1 + 1 / n : ℝ)^n) (hy : y = (1 + 1 / n : ℝ)^(n + 1)) :
    y^x = x^y := calc
  -- We have y^x = ((1 + 1 / n)^(n * (1 + 1 / n)))^x
  --             = ((1 + 1 / n)^n)^((1 + 1 / n) * x)
  --             = x^((1 + 1 / n) * (1 + 1 / n)^n)
  --             = x^y.
  y^x = ((1 + 1 / n)^(n * (1 + 1 / n : ℝ)))^x := by
    rw [hy, ← Real.rpow_natCast]
    congr
    field_simp
  _ = ((1 + 1 / n)^n) ^ ((1 + 1 / n : ℝ) * x) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity), mul_assoc]
  _ = x^y := by
    rw [← hx]
    congr
    rw [hy, pow_succ, ← hx, mul_comm]