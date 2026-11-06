import Mathlib

theorem algebra_56 {x : ℝ} (hx : x = 7 / Real.sqrt 98) : 1/2 * 1/x = Real.sqrt 2 / 2 := by
  rw [hx]
  have h1 : Real.sqrt 98 = 7 * Real.sqrt 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  rw [h1]
  field_simp
  <;> ring_nf <;> norm_num