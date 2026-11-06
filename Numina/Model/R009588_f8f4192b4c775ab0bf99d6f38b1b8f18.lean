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
IsLeast {(n : ℕ) | ((3 : ℝ) / 4) ^ n < 1/ 4} 5 := by
  constructor
  · -- Show that 5 belongs to the set
    norm_num
  · -- Show that 5 is the smallest such element
    intro n hn
    have h : ((3 : ℝ) / 4) ^ n < 1 / 4 := by
      simpa using hn
    by_contra h'
    push_neg at h'
    interval_cases n <;> norm_num at h ⊢ <;> all_goals
      norm_num at h ⊢