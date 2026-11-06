import Mathlib

/- Given that $x + y = 13$ and $xy = 24$, find the distance from the point $(x, y)$ to the origin. -/
theorem algebra_21650 {x y : ℝ} (h₀ : x + y = 13) (h₁ : x * y = 24) :
    Real.sqrt (x ^ 2 + y ^ 2) = 11 := by 
  rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [h₀]