import Mathlib

/- The function $f(x)$ satisfies
\[3f(x) - 2 f \left( \frac{1}{x} \right) = x\]for all $x \neq 0.$  Find $f(4).$ -/
theorem algebra_12053 {f : ℝ → ℝ} (h : ∀ x ≠ 0, 3 * f x - 2 * f (1 / x) = x) :
    f 4 = 5 / 2 := by
  have h₁ := h 4
  have h₂ := h (1 / 4)
  norm_num at h₁ h₂
  linarith