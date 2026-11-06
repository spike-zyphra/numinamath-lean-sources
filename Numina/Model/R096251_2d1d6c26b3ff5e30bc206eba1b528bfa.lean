import Mathlib

theorem number_theory_3197 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1 2020 ∧ 4 ∣ n ∧ ¬26 ∣ n} = 467 := by 
  have : {n : ℕ | n ∈ Finset.Icc 1 2020 ∧ 4 ∣ n ∧ ¬26 ∣ n} = Finset.filter (fun n ↦ 4 ∣ n ∧ ¬26 ∣ n) (Finset.Icc 1 2020) := by
    ext n
    simp 
  rw [this]
  rw [Set.ncard_coe_Finset]
  native_decide