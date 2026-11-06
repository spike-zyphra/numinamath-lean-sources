import Mathlib

theorem inequalities_235834 (O : ℕ) (hO : O ≠ 0) (x : ℕ) (hx : x ≠ 0)
    (h : O / 11 < 7 / x ∧ 7 / x < 4 / 5) :
    O + x ≤ 77 := by
  norm_num at h