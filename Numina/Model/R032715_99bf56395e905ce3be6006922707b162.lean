import Mathlib

theorem number_theory_233733 {n : ℕ} (hn : n ≠ 0) (h : 100 % n = 4 ∧ 90 % n = 18) :
    n = 24 := by
  rcases h with ⟨h1, h2⟩
  have h1' : n ≤ 100 := by
    by_contra h1'
    push_neg at h1'
    have : 100 % n = 100 := by
      rw [Nat.mod_eq_of_lt]
      linarith
    omega
  -- Now n ≤ 100
  have h11 : n ≤ 90 := by
    by_contra h11
    push_neg at h11
    have : 90 % n = 90 := by
      rw [Nat.mod_eq_of_lt]
      linarith
    omega
  interval_cases n <;> omega