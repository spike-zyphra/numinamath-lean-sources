import Mathlib

theorem algebra_123063 {V W : ℝ} (hV : V > 0) (hW : W > 0)
    (h1 : (W - V) * t1 = 1) (h2 : (W + V) * t2 = 1)
    (ht1 : t1 = 1 / (W - V)) (ht2 : t2 = 1 / (W + V))
    (h3 : V * (t1 + t2) = 1) :
    W * (t1 + t2) = 1 + Real.sqrt 2 := by

  have eq1 : W - V ≠ 0 := by 
    by_contra h
    have h4 : (W - V) * t1 = 0 := by
      rw [show W - V = 0 by linarith]
      simp
    linarith [h1, h4]
  
  have eq2 : W + V ≠ 0 := by 
    by_contra h
    have h5 : (W + V) * t2 = 0 := by
      rw [show W + V = 0 by linarith]
      simp
    linarith [h2, h5]
    
  have h4 : t1 + t2 = 1 / (W - V) + 1 / (W + V) := by 
    rw [ht1, ht2]
  
  have h5 : V * (t1 + t2) = 1 := h3
  rw [h4] at h5
  
  have h7 : W ^ 2 - 2 * V * W - V ^ 2 = 0 := by
    have eq3 : V * (1 / (W - V) + 1 / (W + V)) = 1 := by linarith
    have eq4 : V * (1 / (W - V) + 1 / (W + V)) = (2 * V * W) / (W^2 - V^2) := by 
      field_simp [(show W - V ≠ 0 by assumption), (show W + V ≠ 0 by assumption), show W^2 - V^2 ≠ 0 by
        by_contra h
        have h8 : W^2 - V^2 = 0 := by linarith
        have h9 : (W - V) * (W + V) = 0 := by
          linarith
        cases' (mul_eq_zero.mp h9) with h10 h11
        · -- W - V = 0
          exfalso
          tauto
        · -- W + V = 0
          exfalso
          nlinarith [hV, hW, show W + V ≥ 0 by nlinarith]
      ]
      <;> ring
    rw [eq4] at eq3
    field_simp [(show W^2 - V^2 ≠ 0 by
      by_contra h
      have h8 : W^2 - V^2 = 0 := by linarith
      have h9 : (W - V) * (W + V) = 0 := by
        linarith
      cases' (mul_eq_zero.mp h9) with h10 h11
      · -- W - V = 0
        exfalso
        tauto
      · -- W + V = 0
        exfalso
        nlinarith [hV, hW, show W + V ≥ 0 by nlinarith]
    )] at eq3 
    <;> nlinarith
  
  have h8 : (W / V)^2 - 2 * (W / V) - 1 = 0 := by
    have h9 : W ^ 2 - 2 * V * W - V ^ 2 = 0 := h7
    have h10 : V > 0 := hV
    have eq2 : (W / V)^2 - 2 * (W / V) - 1 = (W ^ 2 - 2 * V * W - V ^ 2) / (V ^ 2) := by 
      field_simp [(show (V: ℝ) ≠ 0 by linarith)]
      <;> ring
    rw [eq2]
    rw [h9]
    norm_num
  
  have h9 : W / V = 1 + Real.sqrt 2 := by
    have h8' : (W / V)^2 - 2 * (W / V) - 1 = 0 := h8
    have h10 : ( (W / V) - (1 + Real.sqrt 2) ) * ( (W / V) - (1 - Real.sqrt 2) ) = 0 := by 
      nlinarith [Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)]
    cases' (mul_eq_zero.mp h10) with h11 h12
    · -- (W / V) - (1 + Real.sqrt 2) = 0
      linarith
    · -- (W / V) - (1 - Real.sqrt 2) = 0
      have h13 : (W / V) = 1 - Real.sqrt 2 := by linarith
      have h15 : Real.sqrt 2 > 1 := by
        have h16 : Real.sqrt 2 > (1 : ℝ) := by
          nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (2 : ℝ) > (0 : ℝ) by norm_num)]
        linarith
      have h16 : (W / V) > (1 : ℝ) := by
        have h17 : W > V := by
          nlinarith [sq_nonneg (W - V), hV, h3, h1, h2, h4, h5]
        have h18 : (W / V) > (V) / (V) := by
          apply (div_lt_div_right (by linarith)).mpr
          linarith [show W > V by linarith]
        have h19 : (V) / (V) = 1 := by
          field_simp [(show (V : ℝ) ≠ 0 by linarith)]
        linarith
      nlinarith [h13, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)]
  
  have h10 : W * (t1 + t2) = (W / V) * (V * (t1 + t2)) := by 
    field_simp [(show (V : ℝ) ≠ 0 by linarith)]
    <;> ring
  
  rw [h10, h9, h3]
  all_goals nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)]