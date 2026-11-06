import Mathlib

open Real

theorem algebra_114848 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : sqrt 2 * x + 1 / (sqrt 2 * x) + sqrt 2 * y + 1 / (sqrt 2 * y) +
      sqrt 2 * z + 1 / (sqrt 2 * z) = 6 - 2 * sqrt (2 * x) * abs (y - z) -
      sqrt (2 * y) * (x - z) ^ 2 - sqrt (2 * z) * sqrt (abs (x - y))) :
    x = y ∧ y = z ∧ z = 1 / sqrt 2 := by

  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h3 : 0 < sqrt 2 * x := mul_pos h2 hx
  have h4 : 0 < sqrt 2 * y := mul_pos h2 hy
  have h5 : 0 < sqrt 2 * z := mul_pos h2 hz

  have h6 : sqrt 2 * x + 1 / (sqrt 2 * x) ≥ 2 := by
    have h7 : sqrt 2 * x > 0 := h3
    have h8 : sqrt 2 * x * (1 / (sqrt 2 * x)) = 1 := by
      field_simp
    nlinarith [sq_nonneg (sqrt 2 * x - 1), Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)]
  
  have h6y : sqrt 2 * y + 1 / (sqrt 2 * y) ≥ 2 := by
    have h7 : sqrt 2 * y > 0 := h4
    have h8 : sqrt 2 * y * (1 / (sqrt 2 * y)) = 1 := by
      field_simp
    nlinarith [sq_nonneg (sqrt 2 * y - 1), Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)]
  
  have h6z : sqrt 2 * z + 1 / (sqrt 2 * z) ≥ 2 := by
    have h7 : sqrt 2 * z > 0 := h5
    have h8 : sqrt 2 * z * (1 / (sqrt 2 * z)) = 1 := by
      field_simp
    nlinarith [sq_nonneg (sqrt 2 * z - 1), Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)]

  have h7 : sqrt 2 * x + 1 / (sqrt 2 * x) = 2 := by
    nlinarith [h1, h6, h6y, h6z, abs_nonneg (y - z), abs_nonneg (x - y), Real.sqrt_nonneg (2 * x), Real.sqrt_nonneg (2 * y), Real.sqrt_nonneg (2 * z), Real.sqrt_nonneg (abs (x - y)), sq_nonneg (sqrt 2 * x - 1), sq_nonneg (sqrt 2 * y - 1), sq_nonneg (sqrt 2 * z - 1), Real.sqrt_nonneg (2), mul_nonneg (Real.sqrt_nonneg (2) ) (Real.sqrt_nonneg (2) ) ]
  
  have h8 : sqrt 2 * y + 1 / (sqrt 2 * y) = 2 := by
    nlinarith [h1, h6, h6y, h6z, abs_nonneg (y - z), abs_nonneg (x - y), Real.sqrt_nonneg (2 * x), Real.sqrt_nonneg (2 * y), Real.sqrt_nonneg (2 * z), Real.sqrt_nonneg (abs (x - y)), sq_nonneg (sqrt 2 * x - 1), sq_nonneg (sqrt 2 * y - 1), sq_nonneg (sqrt 2 * z - 1), Real.sqrt_nonneg (2), mul_nonneg (Real.sqrt_nonneg (2) ) (Real.sqrt_nonneg (2) ) ]
  
  have h9 : sqrt 2 * z + 1 / (sqrt 2 * z) = 2 := by
    nlinarith [h1, h6, h6y, h6z, abs_nonneg (y - z), abs_nonneg (x - y), Real.sqrt_nonneg (2 * x), Real.sqrt_nonneg (2 * y), Real.sqrt_nonneg (2 * z), Real.sqrt_nonneg (abs (x - y)), sq_nonneg (sqrt 2 * x - 1), sq_nonneg (sqrt 2 * y - 1), sq_nonneg (sqrt 2 * z - 1), Real.sqrt_nonneg (2), mul_nonneg (Real.sqrt_nonneg (2) ) (Real.sqrt_nonneg (2) ) ]
  
  have h10 : sqrt 2 * x = 1 := by
    have h7 : sqrt 2 * x + 1 / (sqrt 2 * x) = 2 := h7
    have h11 : sqrt 2 * x > 0 := h3
    field_simp at h7 ⊢
    nlinarith [ Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num) ]
  
  have h11 : sqrt 2 * y = 1 := by
    have h7 : sqrt 2 * y + 1 / (sqrt 2 * y) = 2 := h8
    have h12 : sqrt 2 * y > 0 := h4
    field_simp at h7 ⊢
    nlinarith [ Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num) ]
  
  have h12 : sqrt 2 * z = 1 := by
    have h7 : sqrt 2 * z + 1 / (sqrt 2 * z) = 2 := h9
    have h13 : sqrt 2 * z > 0 := h5
    field_simp at h7 ⊢
    nlinarith [ Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num) ]
  
  have hx1 : x = 1 / sqrt 2 := by
    have h14 : sqrt 2 * x = 1 := h10
    field_simp at h14 ⊢
    all_goals nlinarith [ Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num) ]
  
  have hy1 : y = 1 / sqrt 2 := by
    have h14 : sqrt 2 * y = 1 := h11
    field_simp at h14 ⊢
    all_goals nlinarith [ Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num) ]
  
  have hz1 : z = 1 / sqrt 2 := by
    have h14 : sqrt 2 * z = 1 := h12
    field_simp at h14 ⊢
    all_goals nlinarith [ Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num) ]
  
  exact ⟨by linarith [hx1, hy1], by linarith [hy1, hz1], hz1⟩