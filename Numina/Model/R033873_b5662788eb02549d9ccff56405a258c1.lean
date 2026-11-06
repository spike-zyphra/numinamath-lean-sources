import Mathlib

theorem algebra_98200 (a r : ℝ) (ha : a = Real.sqrt 2) (hr : r ≠ 0)
    (h : a * r = 2 ^ ((1 : ℝ) / 3)) (h' : a * r ^ 2 = 2 ^ ((1 : ℝ) / 6)) :
    a * r ^ 3 = 1 := by
  have ha2 : a = (2 : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [ha]
    have h1 : Real.sqrt 2 = (2 : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow]
    linarith
  have h1 : r = (2 : ℝ) ^ ((-1 : ℝ) / 6) := by
    have eq1 : a * r = (2 : ℝ) ^ ((1 : ℝ) / 3) := h
    have eq2 : a * r ^ 2 = (2 : ℝ) ^ ((1 : ℝ) / 6) := h'
    rw [ha2] at eq1 eq2
    have h2 : r > 0 := by
      nlinarith [ h, ha2, Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0), Real.rpow_pos_of_pos (show (2 : ℝ) > 0 by norm_num) (1 / 3), Real.rpow_pos_of_pos (show (2 : ℝ) > 0 by norm_num) (1 / 6) ]
    have h3 : r ^ 2 = (2 : ℝ) ^ ((-1 : ℝ) / 3) := by
      have eq3 : ( (2 : ℝ) ^ ((1 : ℝ) / 2) ) * r ^ 2 = (2 : ℝ) ^ ((1 : ℝ) / 6) := by
        linarith [eq2]
      have h3 : r ^ 2 = ( (2 : ℝ) ^ ((1 : ℝ) / 6) ) / ( (2 : ℝ) ^ ((1 : ℝ) / 2) ) := by
        field_simp [(show (2 : ℝ) ^ ((1 : ℝ) / 2) ≠ 0 by positivity)]
        nlinarith [eq3]
      rw [h3]
      have h2_eq : ( (2 : ℝ) ^ ((1 : ℝ) / 6) ) / ( (2 : ℝ) ^ ((1 : ℝ) / 2) ) = (2 : ℝ) ^ ((-1 : ℝ) / 3) := by
        rw [← Real.rpow_sub]
        norm_num
        all_goals norm_num
      linarith [h2_eq]
    have h10 : r = Real.sqrt ( (2 : ℝ) ^ ((-1 : ℝ) / 3) ) := by
      have h11 : r ^ 2 = (2 : ℝ) ^ ((-1 : ℝ) / 3) := h3
      have h12 : r ≥ 0 := by linarith [ h2 ]
      have h13 : Real.sqrt ( r ^ 2 ) = Real.sqrt ( (2 : ℝ) ^ ((-1 : ℝ) / 3) ) := by
        rw [ h3 ]
      have h14 : Real.sqrt ( r ^ 2 ) = r := by
        rw [ Real.sqrt_sq ]
        linarith
      rw [ h14 ] at h13
      linarith
    rw [ h10 ]
    have h20 : Real.sqrt ( (2 : ℝ) ^ ((-1 : ℝ) / 3) ) = (2 : ℝ) ^ ((-1 : ℝ) / 6) := by
      rw [ Real.sqrt_eq_rpow, ← Real.rpow_mul ]
      ring_nf
      all_goals norm_num
    linarith [h20]
  rw [ha2, h1]
  have h21 : ( (2 : ℝ) ^ ((1 : ℝ) / 2) ) * ( ( ( (2 : ℝ) ^ ((-1 : ℝ) / 6) ) ) ^ 3 ) = 1 := by
    have h22 : ( ( (2 : ℝ) ^ ((-1 : ℝ) / 6) ) ^ 3 ) = (2 : ℝ) ^ ((-3 : ℝ) / 6) := by
      rw [ ← Real.rpow_natCast, ← Real.rpow_mul ]
      ring_nf
      all_goals norm_num
    rw [h22]
    have h23 : ( (2 : ℝ) ^ ((1 : ℝ) / 2) ) * ( (2 : ℝ) ^ ((-3 : ℝ) / 6) ) = (2 : ℝ) ^ ( (1 : ℝ) / 2 + (-3 : ℝ) / 6 ) := by
      rw [ ← Real.rpow_add ]
      ring_nf
      all_goals norm_num
    rw [ h23 ]
    norm_num
  linarith [h21]