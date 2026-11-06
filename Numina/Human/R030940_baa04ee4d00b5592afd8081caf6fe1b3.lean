import Mathlib

/- Suppose 6 wallops = 5 ballops. Also suppose 3 ballops = 11 fallops. How many wallops are equivalent to 110 fallops? -/
theorem algebra_21406 {a b c : ℝ} (h₀ : 6*a=5*b) (h₁ : 3*b=11*c) :
    36*a=110*c := by linarith
