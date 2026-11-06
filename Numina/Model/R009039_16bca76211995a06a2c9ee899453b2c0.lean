import Mathlib

theorem number_theory_610822 : ∑ n ∈ (Finset.Icc 9 999).filter (fun x => 9 ∣ x), (Nat.digits 10 n).sum = 1512 := by 
  native_decide