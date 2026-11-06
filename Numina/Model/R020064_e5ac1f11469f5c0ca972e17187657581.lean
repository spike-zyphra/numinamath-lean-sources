import Mathlib

theorem algebra_21498 : (Nat.card {x | 25 ≤ x ∧ x ≤ 100}) = 76 := by
  have h : {x | 25 ≤ x ∧ x ≤ 100} = Finset.Icc 25 100 := by
    ext n
    simp
    <;> omega
  rw [h]
  rw [Nat.card_eq_fintype_card]
  simp
  <;> native_decide