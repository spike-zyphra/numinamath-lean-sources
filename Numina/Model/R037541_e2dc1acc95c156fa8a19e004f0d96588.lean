import Mathlib

theorem algebra_196447 : Real.tan (2 * Real.arccos (5 / Real.sqrt 26) - Real.arcsin (12 / 13)) = -119 / 120 := by
  have h1 : Real.cos (Real.arccos (5 / Real.sqrt 26)) = 5 / Real.sqrt 26 := by
    apply Real.cos_arccos
    · -- Show 5 / Real.sqrt 26 ≥ -1
      have h1 : 5 / Real.sqrt 26 ≥ -1 := by
        have h2 : Real.sqrt 26 > 0 := by positivity
        have h3 : 5 / Real.sqrt 26 ≥ -1 := by
          apply (le_div_iff₀ (by positivity)).mpr
          nlinarith [Real.sqrt_nonneg 26, Real.sq_sqrt (show (0 : ℝ) ≤ 26 by norm_num)]
        linarith
      linarith
    · -- Show 5 / Real.sqrt 26 ≤ 1
      have h1 : 5 / Real.sqrt 26 ≤ 1 := by
        have h2 : Real.sqrt 26 ≥ 5 := by
          nlinarith [Real.sqrt_nonneg 26, Real.sq_sqrt (show (0 : ℝ) ≤ 26 by norm_num), Real.sqrt_nonneg 26]
        have h3 : Real.sqrt 26 > 0 := by positivity
        apply (div_le_iff₀ (by positivity)).mpr
        nlinarith [Real.sqrt_nonneg 26, Real.sq_sqrt (show (0 : ℝ) ≤ 26 by norm_num)]
      linarith

  have h2 : Real.sin (Real.arccos (5 / Real.sqrt 26)) = 1 / Real.sqrt 26 := by
    have h3 : Real.sin (Real.arccos (5 / Real.sqrt 26)) = Real.sqrt (1 - (5 / Real.sqrt 26) ^ 2) := by
      rw [Real.sin_arccos]
    rw [h3]
    have h4 : (5 / Real.sqrt 26 : ℝ) ^ 2 = 25 / 26 := by
      have h5 : (Real.sqrt 26 : ℝ) ^ 2 = 26 := Real.sq_sqrt (by norm_num)
      field_simp [h5]
      all_goals
        nlinarith
    rw [h4]
    have h5 : Real.sqrt (1 - (25 / 26 : ℝ)) = Real.sqrt (1 / 26 : ℝ) := by ring_nf
    rw [h5]
    have h6 : Real.sqrt ((1 / 26 : ℝ)) = (1 / Real.sqrt 26 : ℝ) := by
      have h7 : Real.sqrt (1 / 26) = Real.sqrt 1 / Real.sqrt 26 := by
        rw [Real.sqrt_div (by norm_num)]
      have h8 : Real.sqrt (1 : ℝ) = 1 := Real.sqrt_one
      rw [h7, h8]
    linarith [h6]

  have h3 : Real.sin (2 * Real.arccos (5 / Real.sqrt 26)) = 10 / 26 := by
    have h7 : Real.sin (2 * Real.arccos (5 / Real.sqrt 26)) = 2 * Real.sin (Real.arccos (5 / Real.sqrt 26)) * Real.cos (Real.arccos (5 / Real.sqrt 26)) := by
      rw [show 2 * Real.arccos (5 / Real.sqrt 26) = 2 * (Real.arccos (5 / Real.sqrt 26)) by ring]
      rw [Real.sin_two_mul]
    rw [h7, h1, h2]
    field_simp
    all_goals
      ring_nf

  have h4 : Real.cos (2 * Real.arccos (5 / Real.sqrt 26)) = 24 / 26 := by
    have h7 : Real.cos (2 * Real.arccos (5 / Real.sqrt 26)) = 2 * (Real.cos (Real.arccos (5 / Real.sqrt 26))) ^ 2 - 1 := by
      rw [show 2 * Real.arccos (5 / Real.sqrt 26) = 2 * (Real.arccos (5 / Real.sqrt 26)) by ring]
      rw [Real.cos_two_mul]
    rw [h7, h1]
    have h5 : (5 / Real.sqrt 26 : ℝ) ^ 2 = 25 / 26 := by
      have h5 : (Real.sqrt 26 : ℝ) ^ 2 = 26 := Real.sq_sqrt (by norm_num)
      field_simp [h5]
      all_goals
        nlinarith
    rw [h5]
    norm_num

  have h5 : Real.sin (Real.arcsin (12 / 13 : ℝ)) = 12 / 13 := by
    apply Real.sin_arcsin
    all_goals norm_num

  have h6 : Real.cos (Real.arcsin (12 / 13 : ℝ)) = 5 / 13 := by
    have h7 : Real.cos (Real.arcsin (12 / 13 : ℝ)) = Real.sqrt (1 - (12 / 13) ^ 2) := by
      rw [Real.cos_arcsin]
    rw [h7]
    have h8 : (12 / 13 : ℝ) ^ 2 = 144 / 169 := by norm_num
    rw [h8]
    have h9 : Real.sqrt (1 - (144 / 169 : ℝ)) = (5 / 13 : ℝ) := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    linarith

  have h7 : Real.sin (2 * Real.arccos (5 / Real.sqrt 26) - Real.arcsin (12 / 13)) = -119 / 169 := by
    rw [Real.sin_sub]
    rw [h3, h4, h5, h6]
    norm_num

  have h8 : Real.cos (2 * Real.arccos (5 / Real.sqrt 26) - Real.arcsin (12 / 13)) = 120 / 169 := by
    rw [Real.cos_sub]
    rw [h4, h3, h6, h5]
    norm_num

  rw [Real.tan_eq_sin_div_cos]
  rw [h7, h8]
  all_goals norm_num