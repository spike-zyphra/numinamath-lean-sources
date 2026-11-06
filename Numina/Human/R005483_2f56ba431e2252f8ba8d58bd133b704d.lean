import Mathlib

/- It turns out that 6 is the smallest juicy integer. Find the next two smallest juicy numbers, and show a decomposition of 1 into unit fractions for each of these numbers. You do not need to prove that no smaller numbers are juicy. -/
theorem number_theory_608460 : (1 = (1:ℝ)/2 + (1:ℝ)/4 + (1:ℝ)/6 + (1:ℝ)/12) ∧ (1 = (1:ℝ)/2 + (1:ℝ)/3 + (1:ℝ)/10 + (1:ℝ)/15)  := by
  /- 12 and 15 are the next two smallist juicy numbers. The decompositions of 1 into unit fractions are as above. -/
  norm_num