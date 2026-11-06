import Mathlib

/- The sum of 25 consecutive even integers is 10,000. 
What is the largest of these 25 consecutive integers?
(A)360    (B)388    (C)412    (D)416   (E)424 -/
theorem algebra_98496 (n : ℕ) (h : Even n) (h' : ∑ i ∈ Finset.range 25, (n + 2 * i) = 10000) :
n + 2 * 24 = 424 := by
--the hypothesis h' gives an equation to solve in n. Then the claim is a check by substitution of the solution of h'.
  norm_num [Finset.sum_range_succ', h] at h'
  omega