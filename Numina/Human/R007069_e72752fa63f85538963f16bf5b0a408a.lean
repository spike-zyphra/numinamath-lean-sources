import Mathlib

/- What is the sum of all of the multiples of 3 between 100 and 200? -/
theorem algebra_19095 : ∑ i in (Finset.Icc 100 200).filter (fun x => 3 ∣ x), i = 4950 := by 
  rfl