import Mathlib

/- Suppose that $f(x)$ is a function such that
\[f(xy) + x = xf(y) + f(x)\]for all real numbers $x$ and $y.$  If $f(-1) = 5$ then compute $f(-1001).$ -/
theorem algebra_14430 {f : ℝ → ℝ} (h : ∀ x y, f (x * y) + x = x * f y + f x) (h' : f (-1) = 5) :
    f (-1001) = 2005 := by
  have h₁ := h 1001 (-1)
  have h₂ := h (-1) (-1)
  have h₃ := h (-1) 1001
  simp at h₁ h₂ h₃
  linarith