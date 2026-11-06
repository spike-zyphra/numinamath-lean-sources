import Mathlib

/- Let $f(x) = 2x+1$ and $g(x) = f(2x) - 3$. What is $g(g(2))$? -/
theorem algebra_20725 {f g : ℝ → ℝ} (hf : f = fun x => 2 * x + 1) (hg : g = fun x => f (2 * x) - 3) :
    g (g (2)) = 22 := by 
  simp only [hf, hg]
  norm_num