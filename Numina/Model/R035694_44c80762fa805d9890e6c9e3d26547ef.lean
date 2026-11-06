import Mathlib

theorem number_theory_12178 :
    {x | x ∈ Finset.Icc 1 4000 ∧ 75 ∣ x ∧ 30 ∣ x ∧ 50 ∣ x}.encard = 26 := by
  have h1 : {x | x ∈ Finset.Icc 1 4000 ∧ 75 ∣ x ∧ 30 ∣ x ∧ 50 ∣ x} = Finset.filter (fun x => 75 ∣ x ∧ 30 ∣ x ∧ 50 ∣ x) (Finset.Icc 1 4000) := by
    ext n
    simp
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide