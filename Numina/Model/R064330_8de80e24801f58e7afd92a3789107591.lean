import Mathlib

theorem number_theory_236918 (n : ℕ) (h₀ : 55 % n = 3) (h₁ : 114 % n = 10) (h₂ : 83 % n = 5) :
    n ≤ 26 := by
  by_contra h
  push_neg at h
  have h3 : n ≤ 55 := by
    by_contra h'
    push_neg at h'
    have h4 : 55 % n = 55 := by
      rw [Nat.mod_eq_of_lt]
      omega
      all_goals omega
    linarith [h₀, h4]
  interval_cases n <;> norm_num at h₀ h₁ h₂ <;> omega