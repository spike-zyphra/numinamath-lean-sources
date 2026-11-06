import Mathlib

open Real

/- On Monday, Millie puts a quart of seeds, 25% of which are millet, into a bird feeder.  On each successive day she 
adds another quart of the same mix of seeds without removing any seeds that are left.  Each day the birds eat only 
25% of the millet in the feeder, but they eat all of the other seeds.  On which day, just after Millie has placed the 
seeds, will the birds find that more than half the seeds in the feeder are millet?
(A) Tuesday(B) Wednesday(C) Thursday(D) Friday(E) Saturday-/

-- We will show that the answer is (D) Friday. Translating the question into an equation, we need to show that the smallest
-- integer n with (3/4)^n < 1/4 is 5.
theorem algebra_93648 :
IsLeast {(n : ℕ) | ((3 : ℝ) / 4) ^ n < 1/ 4} 5 := by {
  constructor
  
  -- We first show that 5 satisfies the inequality, which is immediate.
  simp
  norm_num

  -- We now show that any number smaller than 5 does not satisfy the inequality. We do this by a simple case distinction
  -- since the phrasing of the question already tells us that the smallest n should be quite small. We thus just need
  -- to evaluate each case. Another way to approach this would be using monotonicity, which would be better if n was large.
  intros n hn
  contrapose hn
  simp at hn
  simp
  rcases hn with hn5 | hn4 | hn3 | hn2 | hn1 | hn0
  all_goals norm_num
  trivial
}