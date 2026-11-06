import Mathlib

/- Percy buys $3$ apples for $6$ dollars, $4$ pears for $16$ dollars, and $1$ watermelon for $5$ dollars. Assuming the rates stay the same, how much would it cost to buy $10$ apples, $3$ pears, and $2$ watermelons?

$\textbf{(A) } 38\qquad\textbf{(B) } 39\qquad\textbf{(C) } 40\qquad\textbf{(D) } 41\qquad\textbf{(E) } 42$ -/
theorem algebra_35777 (a p w : ℝ) (ha : 3 * a = 6) (hp : 4 * p = 16) (hw : 1 * w = 5) :
    10 * a + 3 * p + 2 * w = 42 := by
  have : a = 2 := by linarith
  have : p = 4 := by linarith
  have : w = 5 := by linarith
  subst_vars
  linarith