import Mathlib

theorem number_theory_177236 (n : ℕ) (hn : n ≠ 0) (h : 55 % n = 3 ∧ 114 % n = 10 ∧ 83 % n = 5) :
    n ≤ 26 := by
  rcases h with ⟨h1, h2, h3⟩
  by_contra h'
  push_neg at h'
  have h4 : n ≤ 55 := by
    by_contra h4
    push_neg at h4
    have h5 : 55 % n = 55 := by
      rw [Nat.mod_eq_of_lt]
      all_goals omega
    omega
  have h5 : n > 26 := by linarith
  interval_cases n <;> norm_num at h1 h2 h3 <;> omega