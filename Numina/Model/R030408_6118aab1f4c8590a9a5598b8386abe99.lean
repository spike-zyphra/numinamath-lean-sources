import Mathlib

theorem number_theory_293622 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ 2 ∣ n ∧ 3 ∣ n ∧ 5 ∣ n ∧ 7 ∣ n ∧ 11 ∣ n} = 4 := by 
  have h1 : {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ 2 ∣ n ∧ 3 ∣ n ∧ 5 ∣ n ∧ 7 ∣ n ∧ 11 ∣ n} = 
    ↑(Finset.filter (fun n => 2 ∣ n ∧ 3 ∣ n ∧ 5 ∣ n ∧ 7 ∣ n ∧ 11 ∣ n) (Finset.Icc 1000 9999)) := by 
    ext n 
    simp 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide