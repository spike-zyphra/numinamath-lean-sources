import Mathlib

set_option linter.unusedVariables false

/-Let $x$ be a natural number greater than 0.
Consider the list of five natural numbers $A = (L_1, L_2, L_3, L_4, L_5)$,
where $L_1=x$, $L_2=x+1$, $L_3=2x+3$, $L_4=3x-1$, and $L_5=x^2$.
Which of the numbers in $A$ add up to the sum $S = 3x+4$?
Show that the answer is the subset $\{L_2, L_3\}$.-/

theorem number_theory_641830 (x L1 L2 L3 L4 L5: ℕ) (h0: 0 < x)
  (h1: L1 = x) (h2: L2 = x + 1) (h3: L3 = 2 * x + 3) (h4: L4 = 3 * x - 1) (h5: L5 = x ^ 2):
  L2 + L3 = 3 * x + 4 := by

  omega