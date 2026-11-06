import Mathlib

theorem number_theory_436 : {n : ℕ | 300 ≤ n ∧ n ≤ 500 ∧ (Nat.digits 10 n).sum = 16}.encard = 13 := by 
  have h1 : {n : ℕ | 300 ≤ n ∧ n ≤ 500 ∧ (Nat.digits 10 n).sum = 16} = 
      Finset.filter (fun n => 300 ≤ n ∧ n ≤ 500 ∧ (Nat.digits 10 n).sum = 16) (Finset.Icc 300 500) := by
    ext n
    simp
    <;> omega
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide