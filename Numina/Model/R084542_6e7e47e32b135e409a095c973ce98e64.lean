import Mathlib

theorem number_theory_108194 (n : ℕ) (h₀ : (Nat.digits 10 n).sum ≡ 0 [MOD 8]) (h₁ : (Nat.digits 10 (n + 2)).sum ≡ 0 [MOD 8]) :
    n ≥ 699 := by
  by_contra h
  push_neg at h
  interval_cases n <;> norm_num [Nat.ModEq] at h₀ h₁ <;> all_goals
    omega