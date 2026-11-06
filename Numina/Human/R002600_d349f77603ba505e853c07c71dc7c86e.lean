import Mathlib

/- Sandwiches at Joe's Fast Food cost $$3$ each and sodas cost $$2$ each. How many dollars will it cost to purchase $5$ sandwiches and $8$ sodas?
$\textbf{(A)}\ 31\qquad\textbf{(B)}\ 32\qquad\textbf{(C)}\ 33\qquad\textbf{(D)}\ 34\qquad\textbf{(E)}\ 35$ -/

theorem Algebra_1164 (h1 : s = 3) (h2 : c = 2) : 5*s + 8*c = 31 := by
--The $5$ sandwiches cost $5\cdot 3=15$ dollars
have H1 : 5*s = 15 := by rw [h1]
--The $8$ sodas cost $8\cdot 2=16$ dollars.
have H2 : 8*c = 16 := by rw [h2]
--In total, the purchase costs $15+16=\boxed{\textbf{(A) }31}$ dollars.
rw[H1, H2]