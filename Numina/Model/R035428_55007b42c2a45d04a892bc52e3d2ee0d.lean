import Mathlib

theorem algebra_165871 (a b : ℝ) (ha : a > 0) (hb : b > 0) (h : a * 16 = b * 11):
    ∃ (n : ℕ), n = 5 ∧ ∃ (k : ℕ), k > 0 ∧ b * k = a * (k + 5) := by
  use 5
  constructor
  · rfl
  use 11
  constructor
  · norm_num
  · -- Show b * k = a * (k + 5)
    norm_num at h ⊢
    linarith