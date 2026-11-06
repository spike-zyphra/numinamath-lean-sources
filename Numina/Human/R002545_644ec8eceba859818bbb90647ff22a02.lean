import Mathlib
/-- What is the value of\[(\log 5)^{3}+(\log 20)^{3}+(\log 8)(\log 0.25)\]where $\log$ denotes the base-ten logarithm?

$\textbf{(A)}~\frac{3}{2}\qquad\textbf{(B)}~\frac{7}{4}\qquad\textbf{(C)}~2\qquad\textbf{(D)}~\frac{9}{4}\qquad\textbf{(E)}~3$ -/
theorem algebra_95117 : (Real.logb 10 5)^3 + (Real.logb 10 20)^3 + (Real.logb 10 8) * (Real.logb 10 0.25) = 2 := by
  -- Let $\text{log } 2 = x$. The expression then becomes\[(1+x)^3+(1-x)^3+(3x)(-2x)=\boxed{2}.\]
  -- expand Real.logb 10 5
  have s1 : Real.logb 10 5 = Real.logb 10 (10 / 2) := by norm_num
  rw [Real.logb_div (by norm_num) (by norm_num)] at s1; norm_num at s1; rw [s1]
  -- expand Real.logb 10 20
  have s2 : Real.logb 10 20 = Real.logb 10 (10 * 2) := by norm_num
  rw [Real.logb_mul (by norm_num) (by norm_num)] at s2; norm_num at s2; rw [s2]
  -- expand Real.logb 10 8
  rw [(by norm_num : (8 : ℝ) = 2 * 2 * 2)]
  repeat rw [Real.logb_mul (by norm_num) (by norm_num)]
  -- expand Real.logb 10 0.25
  norm_num; rw [Real.logb_div (by norm_num) (by norm_num)]; rw [(by norm_num : (4 : ℝ) = 2 * 2)]; repeat rw [Real.logb_mul (by norm_num) (by norm_num)]
  -- conclude
  ring_nf; norm_num