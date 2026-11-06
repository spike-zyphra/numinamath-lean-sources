import Mathlib

theorem number_theory_325776 :
    Set.ncard {n : ℤ | 1 ≤ n ∧ n ≤ 2012 ∧ 5 ∣ (n^2 - n + 3) * (n^2 + n + 3)} = 1610 := by 
  have : {n : ℤ | 1 ≤ n ∧ n ≤ 2012 ∧ 5 ∣ (n^2 - n + 3) * (n^2 + n + 3)} = Finset.filter (fun n => 1 ≤ n ∧ n ≤ 2012 ∧ 5 ∣ (n^2 - n + 3) * (n^2 + n + 3)) (Finset.Icc (-100000 : ℤ) 100000) := by 
    ext n
    simp 
    omega
  rw [this]
  rw [Set.ncard_coe_Finset]
  native_decide