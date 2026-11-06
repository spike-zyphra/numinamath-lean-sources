import Mathlib

theorem number_theory_138649 (x y z : ℕ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h : (x * y * z) / 2 * 40 / 100 = x * y * z) :
    (x = 2 ∧ y = 3 ∧ z = 5) ∨ (x = 2 ∧ y = 5 ∧ z = 6) := by
  have h1 : x * y * z > 0 := mul_pos (mul_pos hx hy) hz
  omega