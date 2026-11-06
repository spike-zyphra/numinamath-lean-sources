import Mathlib

theorem number_theory_13042 : {n : ℕ | n ≤ 20170803 ∧ Nat.Coprime n (20170803)}.encard = 13419464 := by
  have h1 : {n : ℕ | n ≤ 20170803 ∧ Nat.Coprime n (20170803)} = Finset.filter (fun x => x ≤ 20170803 ∧ Nat.Coprime x 20170803) (Finset.Icc (0:ℕ) 20170803) := by
    ext n
    simp
    <;> tauto
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide