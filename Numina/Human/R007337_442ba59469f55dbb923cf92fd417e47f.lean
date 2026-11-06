import Mathlib

/- The function $f(x)$ satisfies
\[f(x) + f \left( \frac{x + 1}{1 - 3x} \right) = x\]for all $x \neq \frac{1}{3}.$  Find $f(2).$ -/
theorem algebra_11235 {f : ℝ → ℝ} (h : ∀ x, x ≠ 1 / 3 → f x + f ((x + 1) / (1 - 3 * x)) = x) :
    f 2 = 48 / 35 := by
  have h₁ := h 2 (by norm_num)
  have h₂ := h ((2 + 1) / (1 - 3 * 2)) (by norm_num)
  have h₃ := h ((2 - 1) / (1 + 3 * 2)) (by norm_num)
  have h₄ := h ((2 + 1) / (1 - 3 * 2)) (by norm_num)
  have h₅ := h ((2 - 1) / (1 + 3 * 2)) (by norm_num)
  norm_num at h₁ h₂ h₃ h₄ h₅
  linarith