import Mathlib

/- What is the sum of all of the multiples of 7 between 100 and 200? -/
theorem algebra_21012 : ∑ n in (Finset.Icc 100 200).filter (fun x => 7 ∣ x), n = 2107 := by 
  rfl
-- correct