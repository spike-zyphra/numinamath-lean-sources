import Mathlib
theorem algebra_94554 (d : ℝ) (h : d > 0) (r t : ℝ)
(hr : r = d / 40) (ht : t = d / 10) :
(d + d) / (r + t) = 16 := by
  have hr1 : r + t = d / 8 := by
    rw [hr, ht]
    linarith
  rw [hr1]
  have h1 : d ≠ 0 := by linarith
  field_simp
  <;> nlinarith