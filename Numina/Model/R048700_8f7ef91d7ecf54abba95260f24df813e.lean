import Mathlib

theorem number_theory_5966 : {x : ℕ | x < 5150 ∧ Nat.Coprime x 5150}.encard = 2040 := by
  have h1 : {x : ℕ | x < 5150 ∧ Nat.Coprime x 5150} = Finset.filter (fun y => Nat.Coprime y 5150) (Finset.Iio (5150 : ℕ)) := by
    ext x
    simp
    <;> tauto
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide