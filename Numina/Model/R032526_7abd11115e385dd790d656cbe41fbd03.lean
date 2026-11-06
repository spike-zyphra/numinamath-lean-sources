import Mathlib

theorem algebra_218572 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : (x ^ ((1 : ℝ) / 3) - y ^ ((1 : ℝ) / 3) - z ^ ((1 : ℝ) / 3)) = 64)
    (h2 : (x ^ ((1 : ℝ) / 4) - y ^ ((1 : ℝ) / 4) - z ^ ((1 : ℝ) / 4)) = 32)
    (h3 : (x ^ ((1 : ℝ) / 6) - y ^ ((1 : ℝ) / 6) - z ^ ((1 : ℝ) / 6)) = 8) :
    False := by
  have h4 : x ^ ((1 : ℝ) / 3) = (x ^ ((1 : ℝ) / 6)) ^ 2 := by
    calc
      x ^ ((1 : ℝ) / 3) = (x ^ ((1 : ℝ) / 6)) ^ (2 : ℝ) := by
        rw [← Real.rpow_mul]
        field_simp
        all_goals linarith
      _ = (x ^ ((1 : ℝ) / 6)) ^ 2 := by
        norm_cast
        <;> norm_num
  have h5 : x ^ ((1 : ℝ) / 4) = (x ^ ((1 : ℝ) / 6)) ^ (3 / 2 : ℝ) := by
    calc
      x ^ ((1 : ℝ) / 4) = x ^ ((1 / 6 : ℝ) * (3 / 2 : ℝ)) := by
        norm_num
      _ = (x ^ ((1 : ℝ) / 6)) ^ (3 / 2 : ℝ) := by
        rw [← Real.rpow_mul]
        ring_nf
        all_goals linarith
  have h6 : z ^ ((1 : ℝ) / 4) = (z ^ ((1 : ℝ) / 6)) ^ (3 / 2 : ℝ) := by
    calc
      z ^ ((1 : ℝ) / 4) = z ^ ((1 / 6 : ℝ) * (3 / 2 : ℝ)) := by
        norm_num
      _ = (z ^ ((1 : ℝ) / 6)) ^ (3 / 2 : ℝ) := by
        rw [← Real.rpow_mul]
        ring_nf
        all_goals linarith
  have h7 : y ^ ((1 : ℝ) / 4) = (y ^ ((1 : ℝ) / 6)) ^ (3 / 2 : ℝ) := by
    calc
      y ^ ((1 : ℝ) / 4) = y ^ ((1 / 6 : ℝ) * (3 / 2 : ℝ)) := by
        norm_num
      _ = (y ^ ((1 : ℝ) / 6)) ^ (3 / 2 : ℝ) := by
        rw [← Real.rpow_mul]
        ring_nf
        all_goals linarith
  have h8 : y ^ ((1 : ℝ) / 3) = (y ^ ((1 : ℝ) / 6)) ^ 2 := by
    calc
      y ^ ((1 : ℝ) / 3) = (y ^ ((1 : ℝ) / 6)) ^ (2 : ℝ) := by
        rw [← Real.rpow_mul]
        field_simp
        all_goals linarith
      _ = (y ^ ((1 : ℝ) / 6)) ^ 2 := by
        norm_cast
        <;> norm_num
  have h9 : z ^ ((1 : ℝ) / 3) = (z ^ ((1 : ℝ) / 6)) ^ 2 := by
    calc
      z ^ ((1 : ℝ) / 3) = (z ^ ((1 : ℝ) / 6)) ^ (2 : ℝ) := by
        rw [← Real.rpow_mul]
        field_simp
        all_goals linarith
      _ = (z ^ ((1 : ℝ) / 6)) ^ 2 := by
        norm_cast
        <;> norm_num
  rw [h4, h8, h9] at h1
  rw [h5, h7, h6] at h2
  have hx6_pos : 0 < x ^ ((1 : ℝ) / 6) := by
    apply Real.rpow_pos_of_pos
    linarith
  have hy6_pos : 0 < y ^ ((1 : ℝ) / 6) := by
    apply Real.rpow_pos_of_pos
    linarith
  have hz6_pos : 0 < z ^ ((1 : ℝ) / 6) := by
    apply Real.rpow_pos_of_pos
    linarith
  nlinarith [sq_nonneg (x ^ ((1 : ℝ) / 6) - y ^ ((1 : ℝ) / 6) - 8), 
    sq_nonneg (x ^ ((1 : ℝ) / 6) - z ^ ((1 : ℝ) / 6) - 8), 
    sq_nonneg (y ^ ((1 : ℝ) / 6) - z ^ ((1 : ℝ) / 6) - 0), 
    Real.rpow_pos_of_pos hx (1 / 6), Real.rpow_pos_of_pos hy (1 / 6), 
    Real.rpow_pos_of_pos hz (1 / 6)]