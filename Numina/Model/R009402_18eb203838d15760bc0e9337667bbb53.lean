import Mathlib

theorem number_theory_17075 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ 8 ∣ n} = 1125 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ 8 ∣ n} = Finset.filter (fun n => 8 ∣ n) (Finset.Icc 1000 9999) := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide