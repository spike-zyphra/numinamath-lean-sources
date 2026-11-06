import Mathlib
/-- What is the value of\[3+\frac{1}{3+\frac{1}{3+\frac13}}?\]$\textbf{(A)}\ \frac{31}{10}\qquad\textbf{(B)}\ \frac{49}{15}\qquad\textbf{(C)}\ \frac{33}{10}\qquad\textbf{(D)}\ \frac{109}{33}\qquad\textbf{(E)}\ \frac{15}{4}$ -/
theorem algebra_93545 : (3 + 1 / (3 + 1 / (3 + 1 / 3)) : ℚ) = 109 / 33 := by
  -- calculation solves the problem
  norm_num