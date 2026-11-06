import Mathlib
/-- Each morning of her five-day workweek, Jane bought either a $50$-cent muffin or a $75$-cent bagel. Her total cost for the week was a whole number of dollars. How many bagels did she buy?

$\textbf{(A) } 1\qquad\textbf{(B) } 2\qquad\textbf{(C) } 3\qquad\textbf{(D) } 4\qquad\textbf{(E) } 5$ -/
theorem number_theory_93624 (x y : ℕ) (h : x + y = 5) (h' : 50 * x + 75 * y = 100 * n) :
y = 2 := by
  -- If Jane bought $1$ bagel, then she bought $4$ muffins. Her total cost for the week would be $75\cdot1+50\cdot4=275$ cents, or $2.75$ dollars. Clearly, she bought one more bagel but one fewer muffin at a total cost of $3.00$ dollars. Therefore, she bought $\boxed{\textbf{(B) } 2}$ bagels.
  omega