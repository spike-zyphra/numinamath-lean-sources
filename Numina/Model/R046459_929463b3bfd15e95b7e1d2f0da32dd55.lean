import Mathlib

theorem algebra_14071 {s : ℝ} (hs : s > 0) (h : s^2 = 325) :
    4 * s = 20 * Real.sqrt 13 := by
  have h1 : s = Real.sqrt 325 := by
    rw [← h]
    field_simp [hs]
  have h2 : Real.sqrt 325 = 5 * Real.sqrt 13 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  calc
    4 * s = 4 * (Real.sqrt 325) := by rw [h1]
    _ = 4 * (5 * Real.sqrt 13) := by rw [h2]
    _ = 20 * Real.sqrt 13 := by ring