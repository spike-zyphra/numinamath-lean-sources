import Mathlib
open Mathlib
/--
At the beginning of the school year, Lisa's goal was to earn an $A$ on at least $80\%$ of her $50$ quizzes for the year.  She earned an $A$ on $22$ of the first $30$ quizzes.  If she is to achieve her goal, on at most how many of the remaining quizzes can she earn a grade lower than an $A$?
$\textbf{(A) }\ 1      \qquad \textbf{(B) }\ 2      \qquad \textbf{(C) }\ 3      \qquad \textbf{(D) }\ 4      \qquad \textbf{(E) }\ 5$
-/
lemma algebra_1163 (total_a remaining_lower_than_a : ℚ) (h1 : total_a = (80 : ℚ) / 100 * 50) (h2 : (22 + (50 - 30 - remaining_lower_than_a)) = total_a) : remaining_lower_than_a = 2 := by
  -- Lisa's goal was to get an $A$ on $80\% \cdot 50 = 40$ quizzes.
  norm_num at h1
  -- She already has $A$'s on $22$ quizzes, so she needs to get $A$'s on $40-22=18$ more. 
  have dd : 50 - 30 - remaining_lower_than_a = 18 := by linarith
  -- There are $50-30=20$ quizzes left, so she can afford to get less than an $A$ on $20-18=\boxed{\textbf{(B) }2}$ of them.
  -- Here, only the $A$'s matter... No complicated stuff!
  norm_num at dd
  have ddd : remaining_lower_than_a = 20 - 18 := by linarith
  norm_num at ddd
  exact ddd