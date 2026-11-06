import Mathlib

theorem number_theory_3011 (n : ℕ) (h₀ : n ≥ 1000) (h₁ : n ≤ 9999)
    (h₂ : n + (Nat.digits 10 n).sum > 2022) :
    n ≥ 1997 := by 
  by_contra h
  push_neg at h
  have h3 : n ≤ 1996 := by linarith
  interval_cases n <;> norm_num at h₂ <;> all_goals contradiction