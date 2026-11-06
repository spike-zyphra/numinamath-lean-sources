import Mathlib
open Real

/- Find the minimum value of the function $y=4x+\frac{25}{x}$ where $x > 0$. -/
theorem algebra_9411 (f : ℝ → ℝ) (hf : f = λ x => 4 * x + 25 / x) :
    IsLeast {y | ∃ x > 0, f x = y} 20 := by
  -- We have two goals:
  -- 1. Prove that there exists a positive real number x such that f x = 20
  -- 2. Prove that f x ≥ 20 for all positive real numbers x
  simp [IsLeast, lowerBounds, hf]
  constructor

  . -- Set x = 5/2
    use 5/2
    norm_num

  . intro x hx
    -- AM-GM inequality:
    -- 4x + 25/x = (4x + 25/x) * (1/2 + 1/2) ≥ 2 * √(4x * 25/x) = 20
    have h : (1/2) * (4*x) + (1/2) * (25/x) ≥ (4*x)^(1/2 : ℝ) * (25/x)^(1/2 : ℝ) := by
      apply geom_mean_le_arith_mean2_weighted <;> try norm_num <;> positivity
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, ← sqrt_mul (by positivity)] at h
    have h1 : 4 * x * (25 / x) = 10^2 := by field_simp; ring
    simp [h1] at h
    linarith
