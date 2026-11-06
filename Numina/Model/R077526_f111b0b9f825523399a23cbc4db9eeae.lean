import Mathlib

theorem algebra_21084 (t : ℝ) (ht : t ≠ 0) :
    (24 * t^3 / (15 * t^4)) * (5 * t^8 / (3 * t^6)) = 8 * t / 3 := by
  field_simp [ht]
  ring_nf
  <;> norm_num
  <;> ring