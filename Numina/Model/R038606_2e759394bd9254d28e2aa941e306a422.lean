import Mathlib

theorem algebra_14357 (a b c : ℝ) (ha : a = 4) (hb : b = 3) (hc : c = 3) :
    (1/2) * a * b * (Real.sin (Real.arccos ((a^2 + b^2 - c^2)/(2*a*b)))) = 2 * Real.sqrt 5 := by
  rw [ha, hb, hc]
  have h1 : (4:ℝ)^2 + (3:ℝ)^2 - (3:ℝ)^2 = 16 := by norm_num
  have h2 : (2:ℝ) * (4:ℝ) * (3:ℝ) = 24 := by norm_num
  have h3 : (4^2 + 3^2 - 3^2)/(2*4*3) = (2/3:ℝ) := by
    rw [show (4^2 + 3^2 - 3^2: ℝ) = 16 by norm_num]
    rw [show (2*4*3: ℝ) = 24 by norm_num]
    norm_num
  have h4 : Real.sin (Real.arccos ((4^2 + 3^2 - 3^2)/(2*4*3))) = Real.sqrt (5)/3 := by
    have h5 : Real.sin (Real.arccos ((4^2 + 3^2 - 3^2)/(2*4*3))) = Real.sqrt (1 - ((4^2 + 3^2 - 3^2)/(2*4*3)) ^2 ) := by
      rw [Real.sin_arccos]
    have h6 : 1 - ((4^2 + 3^2 - 3^2)/(2*4*3)) ^2 = (5/9: ℝ) := by
      rw [show (4^2 + 3^2 - 3^2 : ℝ) / (2 * 4 * 3) = (2 / 3 : ℝ) by
        norm_num
      ]
      norm_num
    have h7 : Real.sqrt (1 - ((4^2 + 3^2 - 3^2)/(2*4*3)) ^2 ) = Real.sqrt (5/9: ℝ) := by
      rw [h6]
    have h8 : Real.sqrt (5/9: ℝ) = Real.sqrt (5)/3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf
      <;> norm_num
    rw [h7, h8] at h5
    linarith [h5]
  rw [h4]
  field_simp
  <;> ring_nf
  <;> norm_num