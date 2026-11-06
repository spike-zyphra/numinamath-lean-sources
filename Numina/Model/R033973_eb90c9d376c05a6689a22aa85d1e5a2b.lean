import Mathlib

theorem algebra_16525 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x * y = 20 * (2 ^ ((1 : ℝ) / 3))) (hxz : x * z = 35 * (2 ^ ((1 : ℝ) / 3)))
    (hyz : y * z = 14 * (2 ^ ((1 : ℝ) / 3))) : x * y * z = 140 := by
  have h1 : (x * y * z) ^ 2 = 19600 := by
    calc
      (x * y * z) ^ 2 = (x * y) * (x * z) * (y * z) := by ring
      _ = (20 * (2 ^ ((1 : ℝ) / 3))) * (35 * (2 ^ ((1 : ℝ) / 3))) * (14 * (2 ^ ((1 : ℝ) / 3))) := by
        rw [hxy, hxz, hyz]
      _ = 20 * 35 * 14 * ((2 ^ ((1 : ℝ) / 3)) * (2 ^ ((1 : ℝ) / 3)) * (2 ^ ((1 : ℝ) / 3))) := by
        ring
      _ = 20 * 35 * 14 * (2 ^ ((1 : ℝ) / 3 * (3 : ℝ))) := by
        rw [← Real.rpow_add, ← Real.rpow_add]
        all_goals norm_num
      _ = 20 * 35 * 14 * (2 : ℝ) := by
        norm_num
      _ = 19600 := by
        norm_num

  have h2 : x * y * z > 0 := by
    positivity

  have h3 : x * y * z = Real.sqrt ((x * y * z) ^ 2) := by
    rw [Real.sqrt_sq (show 0 ≤ x * y * z by linarith)]

  have h4 : Real.sqrt ((x * y * z) ^ 2) = 140 := by
    rw [h1]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num

  rw [h3, h4]