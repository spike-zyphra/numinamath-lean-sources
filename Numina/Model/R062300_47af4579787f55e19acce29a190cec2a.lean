import Mathlib

theorem number_theory_4593 : ∑ x in (Finset.Ioo 200 400).filter (fun x => 7 ∣ x), x = 8729 := by 
  native_decide