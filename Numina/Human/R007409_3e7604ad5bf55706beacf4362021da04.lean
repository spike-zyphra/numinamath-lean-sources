import Mathlib

/- Suppose $f(x)$ is a rational function such that $3f\left(\dfrac{1}{x}\right)+\dfrac{2f(x)}{x}=x^2$ for $x\neq 0$.  Find $f(-2)$. -/
theorem algebra_13477 {f : ℝ → ℝ} (hf : ∃ p q : Polynomial ℝ, f = fun x => p.eval x / q.eval x)
    (h : ∀ x ≠ 0, 3 * f (1 / x) + 2 * f x / x = x ^ 2) : f (-2) = 67 / 20 := by 
  rcases hf with ⟨p, q, hf⟩
  have := h (-2)
  have := h (1 / -2)
  simp at *
  norm_num at *
  linarith