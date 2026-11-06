import Mathlib

/--
Which of the following is equal to $1 + \frac {1}{1 + \frac {1}{1 + 1}}$?
$\textbf{(A)}\ \frac {5}{4} \qquad \textbf{(B)}\ \frac {3}{2} \qquad \textbf{(C)}\ \frac {5}{3} \qquad \textbf{(D)}\ 2 \qquad \textbf{(E)}\ 3$
-/
theorem algebra_1201 : 1 + (1 : ℚ) / (1 + (1 : ℚ) / (1 + 1)) = (5 : ℚ) / 3 := by
  -- We compute: \begin{align*} 1 + \frac {1}{1 + \frac {1}{1 + 1}} &= 1 + \frac {1}{1 + \frac {1}{1 + 1}}
  -- \\ &= 1 + \frac {1}{1 + \frac 12}
  rw [(by norm_num : (1 : ℚ) / (1 + 1) = (1 : ℚ) / 2)]
  -- \\ &= 1 + \frac {1}{\frac 32}
  rw [(by norm_num : 1 + (1 : ℚ) / 2 = (3 : ℚ) / 2)]
  -- \\ &= 1 + \frac 23
  rw [(by norm_num : (1 : ℚ) / ((3 : ℚ) / 2) = (2 : ℚ) / 3)]
  -- \\ &= \frac 53 \end{align*}
  norm_num