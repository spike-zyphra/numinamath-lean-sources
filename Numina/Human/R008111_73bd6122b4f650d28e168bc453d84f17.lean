import Mathlib

/-
Problem

"The sum of $x$ and $5$ is a non-positive number." Express this as an inequality.
-/

/-
Solution

**Analysis**: Understanding that a non-positive number means it is less than or equal to $0$.

Thus, the inequality that represents "The sum of $x$ and $5$ is a non-positive number" is:

$$x + 5 ≤ 0$$

Therefore, the answer is $\boxed{x + 5 \leq 0}$.
-/


theorem algebra_9044 (x : ℝ) (h : x + 5 ≤ 0) : x ≤ -5 := by 
  -- just move the term by the property of inequality
  exact le_neg_iff_add_nonpos_right.mpr h