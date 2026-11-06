import Mathlib

theorem number_theory_280390 : {n : ℕ | n ∈ Finset.Icc 10 99 ∧ 7 ∣ n}.encard = 13 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 10 99 ∧ 7 ∣ n} = Finset.filter (fun n => 7 ∣ n) (Finset.Icc 10 99) := by 
    ext n 
    simp 
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide