import Mathlib

/- Albert writes down all of the multiples of 9 between 9 and 999, inclusive. Compute the sum of the digits he wrote.-/
theorem number_theory_610822 : ∑ n ∈ (Finset.Icc 9 999).filter (fun x => 9 ∣ x), (Nat.digits 10 n).sum = 1512 := by
  native_decide