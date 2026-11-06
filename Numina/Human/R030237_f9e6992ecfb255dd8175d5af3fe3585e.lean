import Mathlib

open Real
/-For all positive integers $n$, let $f(n)=\log_{2002} n^2$. Let $N=f(11)+f(13)+f(14)$. Which of the following relations is true?
$\text{(A) }N<1 \qquad \text{(B) }N=1 \qquad \text{(C) }1< N<2 \qquad \text{(D) }N=2 \qquad \text{(E) }N>2$-/
theorem algebra_95336 {f : ℕ → ℝ} (hf : ∀ n, f n = logb 2002 (n ^ 2)) : f 11 + f 13 + f 14 = 2 := by 
--We substitute the definition of f.
  rw[hf,hf,hf]
--Sum of log is the log of multiplication 
  rw[←logb_mul,←logb_mul]
--We prove the logarithm with base 2022 is 2 by proving it equals to 2022^2.
  rw[logb_eq_iff_rpow_eq]
  all_goals
  norm_num