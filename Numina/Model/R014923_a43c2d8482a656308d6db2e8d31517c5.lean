import Mathlib

theorem number_theory_268768 : {n | n ≤ 81 ∧ Nat.Coprime n 81}.encard = 54 := by
  have h1 : {n | n ≤ 81 ∧ Nat.Coprime n 81} = Finset.filter (fun n => Nat.Coprime n 81) (Finset.Iic 81) := by
    ext n
    simp
    <;> tauto

  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide