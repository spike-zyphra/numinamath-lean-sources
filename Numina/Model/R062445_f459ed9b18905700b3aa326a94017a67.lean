import Mathlib

theorem number_theory_7102 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ 7 ∣ n ∧ ¬13 ∣ n} = 1187 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ 7 ∣ n ∧ ¬13 ∣ n} = Finset.filter (fun n => 7 ∣ n ∧ ¬13 ∣ n) (Finset.Icc 1000 9999) := by 
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide