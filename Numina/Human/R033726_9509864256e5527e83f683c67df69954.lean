import Mathlib

/- The Amaco Middle School bookstore sells pencils costing a whole number of cents. 
Some seventh graders each bought a pencil, paying a total of 1.43 dollars. 
Some of the 30 sixth graders each bought a pencil, and they paid a total of 1.95 dollars. 
How many more sixth graders than seventh graders bought a pencil?
(A) 1(B) 2(C) 3(D) 4(E) 5 -/
theorem number_theory_96705 {x y : ℕ} (hx : x = 143) (hy : y = 195) :
(y - x) = 4 * gcd x y := by 
--the difference of the total cost of the pens must be equal to the cost of the pen times the difference in number of people.
--the problem provides all the informations, it is a matter of rewriting and arithmetic operations.
  rw[hx, hy]
  rfl