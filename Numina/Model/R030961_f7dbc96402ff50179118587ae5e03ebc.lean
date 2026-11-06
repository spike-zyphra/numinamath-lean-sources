import Mathlib

theorem algebra_57220 (t c : ℕ) (ht : t + 5 = 2 * (c + 5)) (hc : t - 13 = 3 * (c - 13)) :
    ∃ x, t - x = 4 * (c - x) := by
  use 19
  omega