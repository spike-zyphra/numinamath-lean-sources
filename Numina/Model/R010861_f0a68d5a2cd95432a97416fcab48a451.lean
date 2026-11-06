import Mathlib

theorem algebra_20249 :
    Set.ncard {n : ℕ | 100 ≤ n ∧ n ≤ 500 ∧ (Nat.digits 10 n).count 3 ≥ 2} = 22 := by
  have : {n : ℕ | 100 ≤ n ∧ n ≤ 500 ∧ (Nat.digits 10 n).count 3 ≥ 2} = Finset.filter (fun n => 100 ≤ n ∧ n ≤ 500 ∧ (Nat.digits 10 n).count 3 ≥ 2) (Finset.Icc 0 500) := by
    ext n
    simp
    omega
  rw [this]
  rw [Set.ncard_coe_Finset]
  native_decide