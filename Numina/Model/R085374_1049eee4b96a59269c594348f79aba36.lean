import Mathlib

theorem algebra_221334 : (Real.sqrt 8 - Real.sqrt 2) * (Real.sqrt 7 - Real.sqrt 3) = Real.sqrt 14 - Real.sqrt 6 := by
  have h1 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num <;> ring_nf <;> norm_num
  have h2 : Real.sqrt 8 - Real.sqrt 2 = Real.sqrt 2 := by
    rw [h1]
    ring_nf <;> norm_num
  have h3 : (Real.sqrt 8 - Real.sqrt 2) * (Real.sqrt 7 - Real.sqrt 3) = (Real.sqrt 2) * (Real.sqrt 7 - Real.sqrt 3) := by
    rw [h2]
  rw [h3]
  have h4 : Real.sqrt 2 * Real.sqrt 7 = Real.sqrt 14 := by
    calc
      Real.sqrt 2 * Real.sqrt 7 = Real.sqrt (2 * 7) := by rw [Real.sqrt_mul (by norm_num)]
      _ = Real.sqrt 14 := by norm_num
  have h5 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
    calc
      Real.sqrt 2 * Real.sqrt 3 = Real.sqrt (2 * 3) := by rw [Real.sqrt_mul (by norm_num)]
      _ = Real.sqrt 6 := by norm_num
  calc
    (Real.sqrt 2) * (Real.sqrt 7 - Real.sqrt 3) = Real.sqrt 2 * Real.sqrt 7 - Real.sqrt 2 * Real.sqrt 3 := by ring
    _ = Real.sqrt 14 - Real.sqrt 6 := by rw [h4, h5]