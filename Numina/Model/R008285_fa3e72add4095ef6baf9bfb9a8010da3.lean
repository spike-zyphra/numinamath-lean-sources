import Mathlib

theorem algebra_12255 : Set.ncard {n : ℕ | 300 ≤ n ∧ n ≤ 500 ∧ (Nat.digits 10 n).sum = 16} = 13 := by 
  have : {n : ℕ | 300 ≤ n ∧ n ≤ 500 ∧ (Nat.digits 10 n).sum = 16} = Finset.filter (fun n => 300 ≤ n ∧ n ≤ 500 ∧ (Nat.digits 10 n).sum = 16) (Finset.Icc 300 500) := by
    ext n
    simp 
    <;> omega 
  rw [this]
  rw [Set.ncard_coe_Finset]
  native_decide