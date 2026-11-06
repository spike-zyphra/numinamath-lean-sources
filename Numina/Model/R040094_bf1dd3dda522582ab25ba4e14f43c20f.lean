import Mathlib

theorem number_theory_22894 :
  Set.encard {n | 0 < n ∧ n < 99 ∧ Nat.Coprime n 99} = 60 := by
  have h1 : {n | 0 < n ∧ n < 99 ∧ Nat.Coprime n 99} = Finset.filter (fun n => 0 < n ∧ n < 99 ∧ Nat.Coprime n 99) (Finset.Icc 0 98) := by
    ext n
    simp
    omega
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide