import Mathlib

theorem algebra_267921 {a : ℝ} (ha : a = (4 ^ ((1 : ℝ) / 3)) + (2 ^ ((1 : ℝ) / 3)) + 1) :
    3 / a + 3 / a ^ 2 + 1 / a ^ 3 = 1 := by

  have h1 : (4 : ℝ) ^ ((1 : ℝ) / 3) = ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by
    have h2 : (4 : ℝ) ^ ((1 : ℝ) / 3) = ( (2 : ℝ) ^ (2 : ℝ) ) ^ ((1 : ℝ) / 3) := by
      norm_num
    rw [h2]
    have h3 : ( (2 : ℝ) ^ (2 : ℝ) ) ^ ((1 : ℝ) / 3) = (2 : ℝ) ^ (2 * ( (1 : ℝ) / 3 ) ) := by
      rw [← Real.rpow_mul]
      ring_nf
      all_goals norm_num
    rw [h3]
    have h4 : (2 : ℝ) ^ (2 * ( (1 : ℝ) / 3 ) ) = ( (2: ℝ ) ^ ((1 : ℝ ) / 3 ) ) ^ 2 := by
      have h5 : ( (2: ℝ ) ^ ((1 : ℝ ) / 3 ) ) ^ 2 = (2 : ℝ) ^ (2 * ( (1 : ℝ) / 3 ) ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals norm_num
      linarith [h5]
    linarith [h4]

  have ha2 : a = ( (2: ℝ ) ^ ((1: ℝ ) / 3) ) ^ 2 + ( (2: ℝ ) ^ ((1: ℝ ) / 3) ) + 1 := by
    rw [ha]
    rw [h1]
    <;> ring

  have hx3 : ( (2 : ℝ ) ^ ((1 : ℝ ) / 3 ) ) ^ 3 = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals norm_num

  have h_eq1 : 3 / a + 3 / a ^ 2 + 1 / a ^ 3 = (3 * a^2 + 3 * a + 1) / a^3 := by 
    field_simp [(show a ≠ 0 by 
      by_contra h_eq
      rw [h_eq] at ha2
      have h2_pos : ( (2: ℝ ) ^ ((1: ℝ ) / 3) ) > 0 := by positivity
      nlinarith 
    )]
    <;> ring

  have h_eq2 : a^3 = 3 * a^2 + 3 * a + 1 := by
    rw [ha2]
    have h2x3 : ( (2: ℝ ) ^ ((1: ℝ ) / 3) ) ^3 = 2 := hx3
    nlinarith [ sq_nonneg ( ( (2: ℝ ) ^ ((1: ℝ ) / 3) ) ^2 - ( (2: ℝ ) ^ ((1: ℝ ) / 3) ) - 1 ), sq_nonneg ( ( (2: ℝ ) ^ ((1: ℝ ) / 3) ) - 1 ), Real.rpow_pos_of_pos (show (0 < (2: ℝ)) by norm_num) (1 / 3), h2x3 ]

  have h_eq3 : (3 * a ^ 2 + 3 * a + 1) / a ^3 = 1 := by
    have h_eq4 : a^3 = 3 * a^2 + 3 * a + 1 := h_eq2
    have ha0 : a ≠ 0 := by
      by_contra h_eq
      rw [h_eq] at ha2
      have h2_pos : ( (2: ℝ ) ^ ((1: ℝ ) / 3) ) > 0 := by positivity
      nlinarith 
    have h_eq5 : (3 * a ^ 2 + 3 * a + 1) = a^3 := by linarith 
    have h3a : (3 * a ^ 2 + 3 * a + 1) / a ^3 = (a^3)/a^3 := by
      rw [h_eq5] 
    rw [h3a] 
    have h_eq0 : a^3 ≠ 0 := by 
      intro h0
      have ha0' : a = 0 := by
        have h1eq : a^3 = 0 := by linarith 
        have eq_zero : a^3 = 0 := by linarith 
        have ha0_zero : a = 0 := by
          have h2 : a^3 = 0 := eq_zero
          simp at h2 ⊢
          all_goals try linarith
        exact ha0_zero 
      tauto
    field_simp [h_eq0]

  rw [h_eq1, h_eq3]