import Mathlib

theorem number_theory_219818 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1000000 9999999 ∧ 9 ∣ n ∧ (n % 100) / 10 = 5} = 10 ^ 5 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 1000000 9999999 ∧ 9 ∣ n ∧ (n % 100) / 10 = 5} = Finset.filter (fun n => 9 ∣ n ∧ (n % 100) / 10 = 5) (Finset.Icc 1000000 9999999) := by 
    ext n
    simp 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide