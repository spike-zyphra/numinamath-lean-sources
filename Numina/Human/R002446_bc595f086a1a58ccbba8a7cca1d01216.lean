import Mathlib

/--
What number is one third of the way from $\frac14$ to $\frac34$?
$\textbf{(A)}\ \frac {1}{3} \qquad \textbf{(B)}\ \frac {5}{12} \qquad \textbf{(C)}\ \frac {1}{2} \qquad \textbf{(D)}\
\frac {7}{12} \qquad \textbf{(E)}\ \frac {2}{3}$
-/
theorem algebra_1203 : (1 : ℚ) / 4 + (1 : ℚ) / 3 * ((3 : ℚ) / 4 - (1 : ℚ) / 4) = (5 : ℚ) / 12 := by
  -- 1 / 4 + 1 / 3 * (3 / 4 - 1 / 4) = 1 / 4 + 1 / 3 * (1 / 2)
  rw [(by norm_num : ((3 : ℚ) / 4 - (1 : ℚ) / 4) = (1 : ℚ) / 2)]
  -- 1 / 4 + 1 / 3 * (1 / 2) = 1/4 + 1/6
  rw [(by norm_num : (1 : ℚ) / 3 * ((1 : ℚ) / 2) = (1 : ℚ) / 6)]
  -- 1 / 4 + 1 / 6 = 3 / 12 + 2 / 12
  rw [(by norm_num : (1 : ℚ) / 4 = (3 : ℚ) / 12), (by norm_num : (1 : ℚ) / 6 = (2 : ℚ) / 12)]
  -- 3 / 12 + 2 / 12 = 5 / 12
  norm_num