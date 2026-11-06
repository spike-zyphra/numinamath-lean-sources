import Mathlib

/- Given that $x$ is real and $x^3+\frac{1}{x^3}=52$, find $x+\frac{1}{x}$. -/
theorem algebra_11672 {x : ℝ} (hx : x ≠ 0) (h : x^3 + 1/x^3 = 52) :
    x + 1/x = 4 := by
  -- Calculate (x + 1/x)^3
  have h0 : (x + 1/x)^3 = x^3 + 1 / x^3 + 3*(x+1/x)*(x*x⁻¹) := by ring
  simp [hx, h, -one_div] at h0
  rw [← sub_eq_zero] at h0
  -- Change variable
  generalize x + 1 / x = t at h0
  -- Solve the cubic equation by factorization
  rw [show t^3 - (52 + 3*t) = (t-4)*(t^2 + 4*t + 13) by ring] at h0
  have h : t ^ 2 + 4 * t + 13 > 0 := by
    linarith [sq_nonneg (t + 2)]
  simp [ne_of_gt h] at h0
  linarith
