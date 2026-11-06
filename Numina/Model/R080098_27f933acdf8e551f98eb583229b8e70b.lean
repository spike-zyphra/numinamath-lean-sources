import Mathlib

theorem number_theory_4121 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 10000 99999 ∧ n % 7 = 5 ∧ n % 11 = 5 ∧ n % 13 = 5} = 90 := by 
  have h1 : {n : ℕ | n ∈ Finset.Icc 10000 99999 ∧ n % 7 = 5 ∧ n % 11 = 5 ∧ n % 13 = 5} = Finset.filter (fun n => n % 7 = 5 ∧ n % 11 = 5 ∧ n % 13 = 5) (Finset.Icc 10000 99999) := by 
    ext n
    simp 
  rw [h1] 
  rw [Set.ncard_coe_Finset]
  native_decide