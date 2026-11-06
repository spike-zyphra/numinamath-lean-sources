import Mathlib

theorem number_theory_195 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1 95 ∧ Odd ((n ^ 2) / 10)} = 19 := by 
  have h1 : {n : ℕ | n ∈ Finset.Icc 1 95 ∧ Odd ((n ^ 2) / 10)} = 
    (Finset.Icc 1 95).filter (fun n => Odd ((n ^ 2) / 10)) := by
    ext n
    simp 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide