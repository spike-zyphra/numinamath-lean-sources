import Mathlib

theorem algebra_1610 (d r t : ℝ) (hr : r = d / 40) (ht : t = d / 10) (hd : d > 0) :
    2 * d / (r + t) = 16 := by
  have h1 : r + t = d / 8 := by
    rw [hr, ht]
    linarith
  rw [h1]
  have h2 : d ≠ 0 := by linarith
  field_simp [h2]
  <;> linarith