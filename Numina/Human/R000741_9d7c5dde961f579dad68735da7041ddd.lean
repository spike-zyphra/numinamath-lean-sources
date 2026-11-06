import Mathlib

/- Let $f(x)=\frac{3x^2+5x+8}{x^2-x+4}$ and $g(x)=x-1$. Find $f(g(x))+g(f(x))$, evaluated when $x=1$. -/
theorem algebra_14497 {f g : ℝ → ℝ} (hf : f = fun x => (3 * x ^ 2 + 5 * x + 8) / (x ^ 2 - x + 4))
    (hg : g = fun x => x - 1) :
    f (g 1) + g (f 1) = 5 := by
  rw [hf, hg]
  norm_num