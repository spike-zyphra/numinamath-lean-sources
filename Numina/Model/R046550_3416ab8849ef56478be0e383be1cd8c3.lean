import Mathlib

  theorem number_theory_42989 :
  Set.ncard {n | 0 < n ∧ n ≤ 1000 ∧ (Nat.digits 10 (Nat.digits 10 n).sum).sum = 5 } = 111 := by
  have h1 : {n | 0 < n ∧ n ≤ 1000 ∧ (Nat.digits 10 (Nat.digits 10 n).sum).sum = 5 } = Finset.filter (fun n => 0 < n ∧ n ≤ 1000 ∧ (Nat.digits 10 (Nat.digits 10 n).sum).sum = 5) (Finset.Icc (0 : ℕ) 1000) := by
    ext n
    simp
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide