import Mathlib

/- If $10\%$ of $\left(x+10\right)$ is $\left(x-10\right)$, what is $10\%$ of $x$?

$\text{(A) }\frac{11}{90}\qquad\text{(B) }\frac{9}{11}\qquad\text{(C) }1\qquad\text{(D) }\frac{11}{9}\qquad\text{(E) }\frac{110}{9}$ -/
theorem algebra_60213 {x : ℝ} (h : 10 / 100 * (x + 10) = x - 10) :
    10 / 100 * x = 11 / 9 := by
  linarith [h]
