import Mathlib

/-
The expected result of an individual die roll is (1+2+3+4+5+6) / 6= 7 / 2. For any particular value of b, if b dice are rolled independently, then the expected sum is (7 / 2) b. Likewise, when we roll a dice, the expected value of their sum b is (7 / 2) a, so the expected value of c is (7 / 2)^2 a. Similar reasoning again shows us that the expected value of a is 7 / 2 and so the expected value of c overall is (7 / 2)^3=343 / 8.
-/
theorem Combinatorics_610969
    (a b c : ℕ)
    (h1 : a = ∑ i ∈ Finset.range 6, (i + 1) * (1 / 6 : ℝ)) 
    (h2 : b = ∑ i ∈ Finset.range 6, ((i + 1) * a) * (1 / 6 : ℝ)) 
    (h3 : c = ∑ i ∈ Finset.range 6, ((i + 1) * b) * (1 / 6 : ℝ)) : 
    (c : ℝ) = (343 / 8 : ℝ) := by 

  -- Compute the first weighted average (arithmetic mean of 1 to 6)
  norm_num at h1

  -- Substitute the value of a into the definition of b
  rw [h1] at h2

  -- Compute the second weighted average
  norm_num at h2

  -- Substitute the value of b into the definition of c
  rw [h2] at h3
  
  -- Compute the third weighted average
  norm_num at h3
  
  -- Verify the resulting equality using linear arithmetic
  linarith