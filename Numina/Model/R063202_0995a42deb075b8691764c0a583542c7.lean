import Mathlib

theorem number_theory_282253 {n : ℕ} (hn : n % 19 = 9 ∧ n % 23 = 7) :
    n ≥ 237 := by
  rcases hn with ⟨h₁, h₂⟩
  by_contra h
  push_neg at h
  -- n < 237
  interval_cases n <;> norm_num at h₁ h₂ <;> all_goals omega