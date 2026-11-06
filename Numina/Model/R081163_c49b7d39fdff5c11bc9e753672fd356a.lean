import Mathlib

theorem number_theory_16103 :
    Set.ncard {n : ℕ | 500 ≤ n ∧ n < 1000 ∧ 3 ∈ Nat.digits 10 n ∧ 4 ∈ Nat.digits 10 n} = 10 := by
  have h1 : {n : ℕ | 500 ≤ n ∧ n < 1000 ∧ 3 ∈ Nat.digits 10 n ∧ 4 ∈ Nat.digits 10 n} = Finset.filter (fun n => 500 ≤ n ∧ n < 1000 ∧ 3 ∈ Nat.digits 10 n ∧ 4 ∈ Nat.digits 10 n) (Finset.Icc (0 : ℕ) 999) := by
    ext n
    simp
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide