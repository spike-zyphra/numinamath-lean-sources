import Mathlib

theorem number_theory_63967 :
    Set.ncard {n : ℕ | 1 ≤ n ∧ n ≤ 100 ∧ Nat.Prime (n - Nat.totient n)} = 13 := by
  have h1 : {n : ℕ | 1 ≤ n ∧ n ≤ 100 ∧ Nat.Prime (n - Nat.totient n)} = Finset.filter (fun n => 1 ≤ n ∧ n ≤ 100 ∧ Nat.Prime (n - Nat.totient n)) (Finset.Icc (0 : ℕ) 100) := by
    ext n
    simp
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide