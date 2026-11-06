import Mathlib

theorem algebra_20881 :
    Set.ncard {x : ℕ | x > 0 ∧ x < 100 ∧ 4 ∣ x ∧ 6 ∣ x} = 8 := by
  have : {x : ℕ | x > 0 ∧ x < 100 ∧ 4 ∣ x ∧ 6 ∣ x} =
    (Finset.Ioo 0 100).filter (λ x => 4 ∣ x ∧ 6 ∣ x) := by
    ext x
    simp
    omega
  rw [this]
  rw [Set.ncard_coe_Finset]
  rfl
