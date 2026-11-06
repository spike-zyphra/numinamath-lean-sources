import Mathlib

theorem number_theory_271242 :
    Set.ncard {y : ℕ | y ∈ Finset.Icc 2000 3000 ∧ (y % 4 = 0 ∧ (y % 100 ≠ 0 ∨ y % 400 = 0))} = 243 := by
  have h1 : {y : ℕ | y ∈ Finset.Icc 2000 3000 ∧ (y % 4 = 0 ∧ (y % 100 ≠ 0 ∨ y % 400 = 0))} = Finset.filter (fun (y : ℕ) => y % 4 = 0 ∧ (y % 100 ≠ 0 ∨ y % 400 = 0)) (Finset.Icc 2000 3000) := by
    ext y
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide