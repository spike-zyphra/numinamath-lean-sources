import Mathlib

theorem algebra_14273 (x y : ℝ) (hx : x > 0) (hy : y > 0)
    (h : x * 20 + y * 12 = 122 ∧ x + y = 8) :
    x = 13 / 4 := by
  cases h with
  | intro h1 h2 =>
    have h3 : y = 8 - x := by linarith
    rw [h3] at h1
    linarith