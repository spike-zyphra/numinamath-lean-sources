import Mathlib

/- Carlos took $70\%$ of a whole pie. Maria took one third of the remainder. What portion of the whole pie was left?

$\textbf{(A)}\ 10\%\qquad\textbf{(B)}\ 15\%\qquad\textbf{(C)}\ 20\%\qquad\textbf{(D)}\ 30\%\qquad\textbf{(E)}\ 35\%$ -/
theorem algebra_93412 (x : ℝ) (hx : x = 70 / 100) :
(1 - x) * (1 - 1 / 3) = 20 / 100 := by
  -- If Carlos took $70\%$ of the pie, there must be $(100 - 70)\% = 30\%$ left. After Maria takes $\frac{1}{3}$ of the remaining $30\%, \ 1 - \frac{1}{3} = \frac{2}{3}$ of the remaining $30\%$ is left
  linarith