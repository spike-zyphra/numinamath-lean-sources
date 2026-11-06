import Mathlib

/- Consider the given functions: $$\begin{array}{ccc}
f(x) & = & 5x^2 - \frac{1}{x}+ 3\\
g(x) & = & x^2-k
\end{array}$$If $f(2) - g(2) = 2$, what is the value of $k$? -/
theorem algebra_10183 {f g : ℝ → ℝ} (hf : f = fun x => 5 * x ^ 2 - 1 / x + 3)
    (hg : g = fun x => x ^ 2 - k) (hfg : f 2 - g 2 = 2) :
    k = -33 / 2 := by 
  simp_all only [hf, hg]
  linarith