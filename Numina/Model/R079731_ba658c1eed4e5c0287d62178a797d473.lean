import Mathlib

theorem number_theory_259723 : ¬ (∀ n : ℕ, 0 < n → Nat.Prime (2 * n ^ 2 + 29)) := by
  intro h
  have h29 := h 29 (by norm_num)
  norm_num at h29
  all_goals contradiction