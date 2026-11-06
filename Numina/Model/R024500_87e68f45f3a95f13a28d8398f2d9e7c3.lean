import Mathlib
open Real

theorem algebra_7385 {x : ℝ} (hx : x ≠ 0) (hx1 : x^2 - 1 ≥ 0) (h : x + sqrt (x^2 - 1) + 1 / (x + sqrt (x^2 - 1)) = 10) :
    x^2 + sqrt (x^4 - 1) + 1 / (x^2 + sqrt (x^4 - 1)) = 50 := by

  have h1 : 1 / (x + sqrt (x ^ 2 - 1)) = x - sqrt (x ^ 2 - 1) := by 
    have hx2 : x + sqrt (x ^ 2 - 1) ≠ 0 := by 
      by_contra h0 
      have h5 : x + sqrt (x ^ 2 - 1) = 0 := by linarith 
      have h6 : sqrt (x ^ 2 - 1) = -x := by nlinarith 
      have h7 : sqrt (x ^ 2 - 1) ≥ 0 := Real.sqrt_nonneg (x ^ 2 - 1)
      have h8 : -x ≥ 0 := by nlinarith 
      have h9 : x ≤ 0 := by nlinarith 
      have h10 : x ^ 2 - 1 ≥ 0 := hx1 
      have h11 : x ^ 2 ≥ 1 := by nlinarith 
      have h12 : sqrt (x ^ 2 - 1) ^ 2 = x ^ 2 - 1 := Real.sq_sqrt (show 0 ≤ x ^ 2 - 1 by linarith)
      have h13 : (-x) ^ 2 = x ^ 2 := by ring 
      nlinarith [Real.sqrt_nonneg (x ^ 2 - 1), h6]

    field_simp [hx2]
    have h8 : (x + sqrt (x ^ 2 - 1)) * (x - sqrt (x ^ 2 - 1)) = 1 := by 
      have h7 : sqrt (x ^ 2 - 1) ^ 2 = x ^ 2 - 1 := Real.sq_sqrt (show 0 ≤ x ^ 2 - 1 by linarith)
      nlinarith [h7]
    linarith

  have h2 : 2 * x = 10 := by 
    have h5 : x + sqrt (x ^ 2 - 1) + 1 / (x + sqrt (x ^ 2 - 1)) = 10 := h 
    rw [h1] at h5 
    have h8 : sqrt (x ^ 2 - 1) ≥ 0 := Real.sqrt_nonneg (x ^ 2 - 1)
    nlinarith

  have hx_val : x = 5 := by linarith

  have hx2 : x^2 = 25 := by 
      rw [hx_val]
      norm_num

  have hx4_sub_1 : x^4 - 1 = 624 := by
    calc 
      x^4 - 1 = (x^2) ^ 2 - 1 := by ring 
      _ = 25^2 - 1 := by rw [hx2]
      _ = 624 := by norm_num

  have h9 : sqrt (x^4 - 1) = sqrt 624 := by 
    rw [hx4_sub_1]

  have h11 : (1 / (25 + sqrt 624) : ℝ) = 25 - sqrt 624 := by 
      have h55 : (25 + sqrt 624) ≠ 0 := by 
        have h99 : sqrt 624 > 0 := by 
          apply Real.sqrt_pos.mpr
          all_goals norm_num 
        nlinarith [Real.sqrt_nonneg 624, h99]
      field_simp [h55]
      have h56 : (25 + sqrt 624) * (25 - sqrt 624) = (1 : ℝ) := by 
        nlinarith [Real.sqrt_nonneg 624, Real.sq_sqrt (show (0 : ℝ) ≤ (624 : ℝ) by norm_num)]
      nlinarith

  have h12 : (25 + sqrt 624 + (1 / (25 + sqrt 624) ) : ℝ ) = 50 := by 
    rw [h11]
    ring

  rw [show x^2 + sqrt (x^4 - 1) = (25 + sqrt 624) by
        have h9a : sqrt (x^4 - 1) = sqrt 624 := h9
        have h25 : x^2 = 25 := hx2
        nlinarith [h9a,h25]
      ]
  linarith [h12]