import Mathlib

theorem number_theory_67591 : {n : ℕ | n < 1998 ∧ Nat.Coprime n 1547}.encard = 1487 := by
  have h : {n : ℕ | n < 1998 ∧ Nat.Coprime n 1547} = Finset.filter (fun n => n < 1998 ∧ Nat.Coprime n 1547) (Finset.Iio (1998 : ℕ)) := by
    ext n
    simp
  rw [h]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide