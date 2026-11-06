import Mathlib

/- Given that the polynomial $3{{x}^{3}}+a{{x}^{3}}+3x+1$ can be divided by ${{x}^{2}}+1$ with a quotient of $3x+1$, then the value of $a$ is ___          ___. -/
theorem algebra_2559 {a : ℝ} (h : ∀ x, (3 * x ^ 3 + a * x ^ 3 + 3 * x + 1) / (x ^ 2 + 1) = 3 * x + 1) :
    a = 1 := by
  have h1 := h 1
  norm_num at h1 
  have h2 := h (-1)
  norm_num at h2
  linarith