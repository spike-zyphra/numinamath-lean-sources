-- Remove this line: This is an autoformalization provide by our model. If it is wrong, you can ignore it and propose your own statement formalization. At the end of the submission, you will be asked if the autoformalization is correct.

import Mathlib

/- Solve the following system of equations: \begin{align*}
3x-5y&=-1.5,\\
7x+2y&=4.7.
\end{align*}Express your answer as an ordered pair $(x,y)$ of decimals. -/
theorem algebra_17205 {x y : ℝ} (h1 : 3 * x - 5 * y = -1.5) (h2 : 7 * x + 2 * y = 4.7) :
    x = 0.5 ∧ y = 0.6 := by 
  norm_num at *
  constructor <;> linarith