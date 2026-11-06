import Mathlib

theorem number_theory_110189 {n : ℕ} (h : n ≠ 0) (h1 : 100 % n = 16) (h2 : 200 % n = 4) :
    n = 28 := by
  have h3 : n ≤ 100 := by
    by_contra h4
    push_neg at h4
    have h5 : 100 % n = 100 := by
      rw [Nat.mod_eq_of_lt]
      all_goals
      omega
    omega
  interval_cases n <;> norm_num at h1 h2 ⊢
  all_goals
    tauto