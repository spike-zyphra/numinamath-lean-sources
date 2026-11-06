import Mathlib

def isGood (n : ℕ) := ∃ k, n = k + (k + 1) ∧ ∃ m, n = m + (m + 1) + (m + 2)

/- If a natural number can be expressed as both the sum of two consecutive natural numbers and the sum of three consecutive natural numbers, it is called a "good number." Please find the "good number" among $2007$, $2008$, $2009$, $2010$, $2011$.

 -/
theorem number_theory_495 : isGood 2007 := by 
  use 1003
  constructor
  · -- Verify that 2007 = 1003 + (1003 + 1)
    norm_num
  · -- Use 668 for m
    use 668
    all_goals norm_num