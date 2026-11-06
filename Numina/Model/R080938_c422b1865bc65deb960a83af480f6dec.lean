import Mathlib

theorem number_theory_187045 :
    Set.ncard {m : ℕ | m ∈ Finset.Icc 100 999 ∧ (Nat.digits 10 m).sum = 12 ∧
      (Nat.digits 10 (2 * m)).sum = 6 ∧ (Nat.digits 10 (2 * m)).length = 3} = 3 := by
  have h1 : {m : ℕ | m ∈ Finset.Icc 100 999 ∧ (Nat.digits 10 m).sum = 12 ∧
      (Nat.digits 10 (2 * m)).sum = 6 ∧ (Nat.digits 10 (2 * m)).length = 3} = Finset.filter (fun m => (Nat.digits 10 m).sum = 12 ∧
      (Nat.digits 10 (2 * m)).sum = 6 ∧ (Nat.digits 10 (2 * m)).length = 3) (Finset.Icc 100 999) := by
    ext m
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide