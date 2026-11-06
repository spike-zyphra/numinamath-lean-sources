import Mathlib

theorem number_theory_110300 {a : ℚ} : 0 ≤ abs a - a := by
  cases le_or_lt 0 a with
  | inl h =>
    rw [abs_of_nonneg h]
    all_goals linarith
  | inr h =>
    rw [abs_of_neg h]
    all_goals linarith