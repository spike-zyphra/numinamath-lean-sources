import Mathlib

theorem number_theory_98694 : {x : ℕ | x ∈ Finset.Icc 1 2015 ∧ 3 ∣ x ∧ (x % 10) = 2}.ncard = 67 := by
  have h1 : {x : ℕ | x ∈ Finset.Icc 1 2015 ∧ 3 ∣ x ∧ (x % 10) = 2} = Finset.filter (fun x => 3 ∣ x ∧ (x % 10) = 2) (Finset.Icc 1 2015) := by
    ext x
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide