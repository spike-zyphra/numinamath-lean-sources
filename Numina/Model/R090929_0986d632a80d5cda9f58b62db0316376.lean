import Mathlib

theorem number_theory_6661 :
    Set.ncard {x : ℕ | 1 ≤ x ∧ x ≤ 2018 ∧ 3 ∣ x ∧ 4 ∣ x ∧ ¬8 ∣ x} = 84 := by

  have h1 : {x : ℕ | 1 ≤ x ∧ x ≤ 2018 ∧ 3 ∣ x ∧ 4 ∣ x ∧ ¬8 ∣ x} = Finset.filter (fun x => 3 ∣ x ∧ 4 ∣ x ∧ ¬8 ∣ x) (Finset.Icc (1 : ℕ) 2018) := by
    ext x
    simp
    <;> omega

  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide