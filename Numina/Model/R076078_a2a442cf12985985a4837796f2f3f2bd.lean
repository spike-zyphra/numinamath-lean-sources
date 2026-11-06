import Mathlib

theorem number_theory_69735 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 2000 2010 ∧ 7 ∣ 2^(2*n) + 2^n + 5} = 4 := by
  
  have h1 : {n : ℕ | n ∈ Finset.Icc 2000 2010 ∧ 7 ∣ 2^(2*n) + 2^n + 5} = Finset.filter (fun n => 7 ∣ 2^(2*n) + 2^n + 5) (Finset.Icc 2000 2010) := by 
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide