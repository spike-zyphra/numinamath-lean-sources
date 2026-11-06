import Mathlib

/- Let $f(x) = Ax - 2B^2$ and $g(x) = Bx$, where $B \neq 0$. If $f(g(1)) = 0$, what is $A$ in terms of $B$? -/
theorem algebra_13529 {A B : ℝ} (hB : B ≠ 0) (f g : ℝ → ℝ)
    (hf : f = fun x => A * x - 2 * B ^ 2) (hg : g = fun x => B * x)
    (hfg : f (g 1) = 0) : A = 2 * B := by
  simp [hf, hg] at hfg
  apply mul_right_cancel₀ hB
  linarith