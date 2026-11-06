import Mathlib

theorem number_theory_12178 :
    {x | x ∈ Finset.Icc 1 4000 ∧ 75 ∣ x ∧ 30 ∣ x ∧ 50 ∣ x}.encard = 26 := by
  have : {x | x ∈ Finset.Icc 1 4000 ∧ 75 ∣ x ∧ 30 ∣ x ∧ 50 ∣ x} = Finset.filter (fun x => 75 ∣ x ∧ 30 ∣ x ∧ 50 ∣ x) (Finset.Icc 1 4000) := by
    ext x
    simp
  rw [this]
  rw [Finset.filter]
  simp [Finset.Icc]
  native_decide