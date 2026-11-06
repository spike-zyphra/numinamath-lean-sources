import Mathlib

/- Suppose $f(x)$ is a rational function such that $3 f\left(\frac{1}{x}\right)+\frac{2 f(x)}{x}=x^{2}$ for $x \neq 0$. Find $f(-2)$. -/
theorem algebra_608387 {f : ℝ → ℝ} (hf : ∃ p q : Polynomial ℝ, f = fun x => p.eval x / q.eval x) (h : ∀ x, x ≠ 0 → 3 * f (1 / x) + (2 * f x) / x = x ^ 2) : f (-2) = (67 / 20 : ℝ) := by
  -- Substitute x = -1 / 2 into the equation.
  have h₁ := h (-1 / 2)
  -- Substitute x = -2 into the equation.
  have h₂ := h (-2)
  simp [-one_div] at h₁ h₂
  -- Solve the simultaneous equation.
  linarith

