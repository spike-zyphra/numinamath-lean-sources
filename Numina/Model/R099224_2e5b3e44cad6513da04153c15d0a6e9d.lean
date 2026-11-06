import Mathlib

theorem number_theory_313516 :
    {x : ℕ | x ∈ Finset.Icc 1 1000000 ∧ 11 ∣ x ∧ ¬13 ∣ x}.ncard > {x : ℕ | x ∈ Finset.Icc 1 1000000 ∧ 13 ∣ x ∧ ¬11 ∣ x}.ncard := by
  have h1 : {x : ℕ | x ∈ Finset.Icc 1 1000000 ∧ 11 ∣ x ∧ ¬13 ∣ x} = Finset.filter (fun x => 11 ∣ x ∧ ¬13 ∣ x) (Finset.Icc 1 1000000) := by
    ext x
    simp
  have h2 : {x : ℕ | x ∈ Finset.Icc 1 1000000 ∧ 13 ∣ x ∧ ¬11 ∣ x} = Finset.filter (fun x => 13 ∣ x ∧ ¬11 ∣ x) (Finset.Icc 1 1000000) := by
    ext x
    simp
  rw [h1, h2]
  rw [Set.ncard_coe_Finset]
  rw [Set.ncard_coe_Finset]
  native_decide