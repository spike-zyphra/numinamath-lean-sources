import Mathlib

theorem number_theory_254562 (k : ℕ) (hk : 1 < k) :
    ∃ n, k ∣ n ∧ n < k ^ 4 ∧ (Nat.digits 10 n).length ≤ 4 ∧
      (Nat.digits 10 n).toFinset.card ≤ 4 := by 
  use 0
  constructor
  · -- Show k divides 0
    exact dvd_zero k
  constructor
  · -- Show 0 < k ^ 4
    have h1 : k ^ 4 > 0 := by
      apply Nat.pow_pos
      linarith
    linarith
  constructor
  · -- Show (Nat.digits 10 0).length ≤ 4
    simp
  · -- Show (Nat.digits 10 0).toFinset.card ≤ 4
    simp