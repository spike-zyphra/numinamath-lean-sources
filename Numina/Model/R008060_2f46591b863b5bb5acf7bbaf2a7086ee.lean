import Mathlib

theorem number_theory_68696 (k : ℕ) (hk : 1 < k) :
    ∃ m, k ∣ m ∧ m < k ^ 4 ∧ (Nat.digits 10 m).toFinset.card ≤ 4 := by
  use 0
  constructor
  · exact dvd_zero k
  constructor
  · -- Show that 0 < k ^ 4
    have h : k ^ 4 > 0 := by
      apply Nat.pow_pos
      linarith
    linarith
  · -- Show that (Nat.digits 10 0).toFinset.card ≤ 4
    simp
    all_goals omega