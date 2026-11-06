import Mathlib

theorem number_theory_15743 :
    Set.encard {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ (Nat.digits 10 n).sum = 9 ∧ 11 ∣ n} = 0 := by
  have : {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ (Nat.digits 10 n).sum = 9 ∧ 11 ∣ n} = Finset.filter (fun n => (Nat.digits 10 n).sum = 9 ∧ 11 ∣ n) (Finset.Icc 1000 9999) := by
    ext n
    simp
  rw [this]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide