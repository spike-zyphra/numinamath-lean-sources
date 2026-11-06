import Mathlib
open Mathlib
/--
Al gets the disease algebritis and must take one green pill and one pink pill each day for two weeks. A green pill costs $$$1$ more than a pink pill, and Al's pills cost a total of $\textdollar 546$ for the two weeks. How much does one green pill cost?
$\textbf{(A)}\ \textdollar 7 \qquad\textbf{(B) }\textdollar 14 \qquad\textbf{(C) }\textdollar 19\qquad\textbf{(D) }\textdollar 20\qquad\textbf{(E) }\textdollar 39$
-/
lemma algebra_1146 (greenPrice pinkPrice : ℕ) (hPink : greenPrice = pinkPrice + 1) (hCost : (greenPrice + pinkPrice) * 7 * 2 = 546) : greenPrice = 20 := by linarith