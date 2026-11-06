import Mathlib

theorem number_theory_271139 :
    Set.ncard {x : ℕ | x ∈ Finset.Icc 1 1000 ∧ (2 ∣ x ∨ 3 ∣ x ∨ 5 ∣ x) ∧ ¬6 ∣ x} = 568 := by
  have h1 : {x : ℕ | x ∈ Finset.Icc 1 1000 ∧ (2 ∣ x ∨ 3 ∣ x ∨ 5 ∣ x) ∧ ¬6 ∣ x} = Finset.filter (fun x => (2 ∣ x ∨ 3 ∣ x ∨ 5 ∣ x) ∧ ¬6 ∣ x) (Finset.Icc 1 1000) := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide