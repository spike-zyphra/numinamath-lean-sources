import Mathlib

theorem algebra_19095 : ∑ i in (Finset.Icc 100 200).filter (fun x => 3 ∣ x), i = 4950 := by
  native_decide