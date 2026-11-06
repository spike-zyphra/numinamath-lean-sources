import Mathlib

theorem number_theory_125944 (n : ℕ) (h₀ : 1941 % n = 2019 % n) (h₁ : 2019 % n = 2136 % n) :
    n ≤ 39 := by
  by_contra h
  push_neg at h
  have h2 : n > 39 := h
  have h3 : n ≤ 2136 := by
    by_contra h4
    push_neg at h4
    have h4' : 1941 % n = 1941 := by
      rw [Nat.mod_eq_of_lt]
      all_goals linarith
    have h4'' : 2019 % n = 2019 := by
      rw [Nat.mod_eq_of_lt]
      all_goals linarith
    have h4''' : 2136 % n = 2136 := by
      rw [Nat.mod_eq_of_lt]
      all_goals linarith
    omega
  interval_cases n <;> norm_num at h₀ h₁ ⊢ <;> all_goals omega