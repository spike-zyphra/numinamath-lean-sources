import Mathlib

/--
What is the [reciprocal](https://artofproblemsolving.com/wiki/index.php/Reciprocal) of $\frac{1}{2}+\frac{2}{3}$?
$\mathrm{(A)}\ \frac{6}{7}\qquad\mathrm{(B)}\ \frac{7}{6}\qquad\mathrm{(C)}\ \frac{5}{3}\qquad\mathrm{(D)}\
3\qquad\mathrm{(E)}\ \frac{7}{2}$
-/
theorem algebra_1190 : (1 : ℚ) / ((1 : ℚ) / 2 + (2 : ℚ) / 3) = (6 : ℚ) / 7 := by
  -- 1 / (1 / 2 + 2 / 3) = 1 / (3 / 6 + 2 / 3)
  rw [(by norm_num : (1 : ℚ) / 2 = (3 : ℚ) / 6)]
  -- 1 / (3 / 6 + 2 / 3) = 1 / (3 / 6 + 4 / 6)
  rw [(by norm_num : (2 : ℚ) / 3 = (4 : ℚ) / 6)]
  -- 1 / (3 / 6 + 4 / 6) = 1 / (7 / 6)
  rw [(by norm_num : (3 : ℚ) / 6 + (4 : ℚ) / 6 = (7 : ℚ) / 6)]
  -- 1 / (7 / 6) = 6 / 7
  norm_num