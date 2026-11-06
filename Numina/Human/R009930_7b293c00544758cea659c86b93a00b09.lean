import Mathlib

/- The functions $f(x) = x^2-2x + m$ and $g(x) = x^2-2x + 4m$ are evaluated when $x = 4$. What is the value of $m$ if $2f(4) = g(4)$? -/
theorem algebra_10219 {f g : ℝ → ℝ} (hf : f = fun x => x ^ 2 - 2 * x + m)
    (hg : g = fun x => x ^ 2 - 2 * x + 4 * m) (h : 2 * f 4 = g 4) :
    m = 4 := by 
  simp [hf, hg] at h
  linarith