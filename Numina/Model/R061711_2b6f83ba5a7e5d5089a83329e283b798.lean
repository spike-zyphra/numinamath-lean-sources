import Mathlib

theorem algebra_151415 {b g : ℕ} (hb : b ≠ 0) (hg : g ≠ 0)
    (h : 7 * b = 6 * 40 + 3 * g) (h' : 3 * g = 4 * 40) :
    b = 10 ∧ g = 10 ∧ 7 * b + 3 * g = 180 := by 
  omega