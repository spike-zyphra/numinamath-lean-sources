import Mathlib

theorem number_theory_3562 (n : ℕ) (h₀ : 0 < n) (h₁ : (n ^ 3) % 10 = 7)
    (h₂ : (n ^ 3) / 100 % 10 = 7) (h₃ : (n ^ 3) / 10000 % 10 = 7) :
    n ≥ 83 := by
  by_contra h
  push_neg at h
  have h4 : n ≤ 82 := by linarith
  interval_cases n <;> norm_num at h₁ h₂ h₃ h₀ <;> all_goals contradiction