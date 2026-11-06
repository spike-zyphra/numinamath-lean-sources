import Mathlib

open Real

theorem algebra_190141 : sin (π / 12) = (sqrt 6 - sqrt 2) / 4 ∧
    cos (π / 12) = (sqrt 6 + sqrt 2) / 4 ∧
    sin (π / 10) = (-1 + sqrt 5) / 4 ∧
    cos (π / 10) = sqrt (10 + 2 * sqrt 5) / 4 := by
  have h1 : sin (π / 12) = (sqrt 6 - sqrt 2) / 4 := by
    have h2 : sin (π / 12) = sin (π / 4 - π / 6) := by 
      ring_nf
    rw [h2]
    have h3 : sin (π / 4 - π / 6) = sin (π / 4) * cos (π / 6) - cos (π / 4) * sin (π / 6) := by 
      rw [sin_sub]
    rw [h3]
    have h4 : sin (π / 4) = Real.sqrt 2 / 2 := by 
      rw [sin_pi_div_four]
    have h5 : cos (π / 4) = Real.sqrt 2 / 2 := by 
      rw [cos_pi_div_four]
    have h6 : sin (π / 6) = 1 / 2 := by 
      rw [sin_pi_div_six]
    have h7 : cos (π / 6) = Real.sqrt 3 / 2 := by 
      rw [cos_pi_div_six]
    rw [h4, h5, h6, h7]
    have h10 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
      have h12 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt (2 * 3 : ℝ) := by
        rw [← Real.sqrt_mul (by norm_num)]
      rw [h12]
      all_goals norm_num
    nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num : (2 : ℝ) > 0), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (3 : ℝ) > 0), 
        Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, 
        Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num : (2 : ℝ) ≥ 0), 
        Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0)
    ]
  have h2 : cos (π / 12) = (sqrt 6 + sqrt 2) / 4 := by
    have h3 : cos (π / 12) = cos (π / 4 - π / 6) := by 
      ring_nf
    rw [h3]
    have h4 : cos (π / 4 - π / 6) = cos (π / 4) * cos (π / 6) + sin (π / 4) * sin (π / 6) := by 
      rw [cos_sub]
    rw [h4]
    have h5 : sin (π / 4) = Real.sqrt 2 / 2 := by 
      rw [sin_pi_div_four]
    have h6 : cos (π / 4) = Real.sqrt 2 / 2 := by 
      rw [cos_pi_div_four]
    have h7 : sin (π / 6) = 1 / 2 := by 
      rw [sin_pi_div_six]
    have h8 : cos (π / 6) = Real.sqrt 3 / 2 := by 
      rw [cos_pi_div_six]
    rw [h5, h6, h7, h8]
    have h10 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
      have h12 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt (2 * 3 : ℝ) := by
        rw [← Real.sqrt_mul (by norm_num)]
      rw [h12]
      all_goals norm_num
    nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num : (2 : ℝ) > 0), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (3 : ℝ) > 0), 
        Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, 
        Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num : (2 : ℝ) ≥ 0), 
        Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0)
    ]
  have h3 : sin (π / 10) = (-1 + sqrt 5) / 4 := by
    have h34 : sin (π / 10) ^ 2 = (3 - Real.sqrt 5) / 8 := by
      have h34 : sin (π / 10) ^ 2 = (1 - cos (π / 5)) / 2 := by
        have h38 : sin (π / 10) ^ 2 = (1 - cos (2 * (π / 10))) / 2 := by 
          rw [sin_sq_eq_half_sub]
          <;> ring
        have h65 : 2 * (π / 10) = π / 5 := by 
          linarith [pi_pos]
        rw [h65] at h38
        linarith [h38]
      rw [h34]
      have h24 : cos (π / 5) = (1 + Real.sqrt 5) / 4 := by 
        rw [cos_pi_div_five]
      rw [h24]
      ring_nf
    have h340 : sin (π / 10) > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [pi_pos]
      linarith [pi_pos]
    have h19 : sin (π / 10) = Real.sqrt ((3 - Real.sqrt 5) / 8) := by
      have h20 : Real.sqrt (sin (π / 10) ^ 2) = Real.sqrt ((3 - Real.sqrt 5) / 8) := by
        rw [h34]
      have h21 : Real.sqrt (sin (π / 10) ^ 2) = sin (π / 10) := by
        rw [Real.sqrt_sq (show 0 ≤ sin (π / 10) by linarith [h340])]
      nlinarith
    -- show sqrt((3 - sqrt 5) / 8) = (sqrt 5 - 1) / 4
    have h31 : Real.sqrt ((3 - Real.sqrt 5) / 8) = (Real.sqrt 5 - 1) / 4 := by
      have h200 : ((Real.sqrt 5 - 1) / 4 : ℝ) ^ 2 = (3 - Real.sqrt 5) / 8 := by
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num : (5 : ℝ) ≥ 0), Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num : (5 : ℝ) > 0)]
      have h201 : ((Real.sqrt 5 - 1) / 4 : ℝ) ≥ 0 := by
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num : (5 : ℝ) ≥ 0), Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num : (5 : ℝ) > 0)]
      have h302 : Real.sqrt (( (Real.sqrt 5 - 1) / 4 ) ^ 2) = ( (Real.sqrt 5 - 1) / 4 ) := by
        apply Real.sqrt_sq
        linarith [h201]
      have h303 : Real.sqrt ((3 - Real.sqrt 5) / 8) = ( (Real.sqrt 5 - 1) / 4 ) := by
        have h304 : Real.sqrt ((3 - Real.sqrt 5) / 8) = Real.sqrt ( ((Real.sqrt 5 - 1) / 4 : ℝ) ^ 2 ) := by
          rw [h200] 
        rw [h304]
        nlinarith [h302]
      linarith
    -- show `sin(π/10) = (sqrt 5 - 1) / 4`
    have h35 : sin (π / 10) = (Real.sqrt 5 - 1) / 4 := by
      nlinarith [h19, h31]
    -- show `sin(π/10) = (-1 + sqrt 5) / 4`
    ring_nf at h35 ⊢
    linarith
  have h4 : cos (π / 10) = sqrt (10 + 2 * sqrt 5) / 4 := by
    have h17 : cos (π / 10) ^ 2 = (5 + Real.sqrt 5) / 8 := by
      have h15 : cos (π / 10) ^ 2 = (1 + cos (π / 5)) / 2 := by
        have h30 : cos (π / 10) ^ 2 = (1 + cos (2 * (π / 10))) / 2 := by 
          rw [cos_sq]
          ring_nf
        have h65 : 2 * (π / 10) = π / 5 := by 
          linarith [pi_pos]
        rw [h65] at h30
        linarith [h30]
      rw [h15]
      have h24 : cos (π / 5) = (1 + Real.sqrt 5) / 4 := by 
        rw [cos_pi_div_five]
      rw [h24]
      ring_nf
    have h18 : 0 < cos (π / 10) := by
      apply cos_pos_of_mem_Ioo
      constructor
      · linarith [pi_pos]
      · linarith [pi_pos]
    have h19 : cos (π / 10) = Real.sqrt ((5 + Real.sqrt 5) / 8) := by
      have h20 : Real.sqrt (cos (π / 10) ^ 2) = Real.sqrt ((5 + Real.sqrt 5) / 8) := by
        rw [h17]
      have h21 : Real.sqrt (cos (π / 10) ^ 2) = cos (π / 10) := by
        rw [Real.sqrt_sq (show 0 ≤ cos (π / 10) by linarith [h18])]
      nlinarith
    -- show `sqrt ((5 + Real.sqrt 5) / 8) = sqrt (10 + 2 * sqrt 5) / 4`
    have h31 : Real.sqrt ((5 + Real.sqrt 5) / 8) = sqrt (10 + 2 * sqrt 5) / 4 := by
      have h200 : (sqrt (10 + 2 * sqrt 5) / 4) ^ 2 = (5 + Real.sqrt 5) / 8 := by
        have h100 : 0 ≤ (10 + 2 * Real.sqrt 5 : ℝ) := by
          nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num : (5 : ℝ) ≥ 0)]
        have h101 : (sqrt (10 + 2 * sqrt 5) : ℝ) ^ 2 = 10 + 2 * Real.sqrt 5 := by
          rw [Real.sq_sqrt]
          linarith
        nlinarith [Real.sqrt_nonneg (10 + 2 * sqrt 5), Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num : (5 : ℝ) ≥ 0), Real.sq_sqrt (show 0 ≤ (10 + 2 * sqrt 5 : ℝ) by 
          nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num : (5 : ℝ) ≥ 0)]
        )
        ]
      have h201 : (sqrt (10 + 2 * sqrt 5) / 4 : ℝ) ≥ 0 := by
        nlinarith [Real.sqrt_nonneg (10 + 2 * sqrt 5), Real.sq_sqrt (show 0 ≤ (10 + 2 * sqrt 5 : ℝ) by 
          nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num : (5 : ℝ) ≥ 0)]
        )
        ]
      have h302 : Real.sqrt ((sqrt (10 + 2 * sqrt 5) / 4 : ℝ) ^ 2) = (sqrt (10 + 2 * sqrt 5) / 4 : ℝ) := by
        apply Real.sqrt_sq
        linarith [h201]
      have h303 : Real.sqrt ((5 + Real.sqrt 5) / 8) = (sqrt (10 + 2 * sqrt 5) / 4 : ℝ) := by
        have h304 : Real.sqrt ((5 + Real.sqrt 5) / 8) = Real.sqrt ((sqrt (10 + 2 * sqrt 5) / 4 : ℝ) ^ 2) := by
          rw [h200] 
        rw [h304]
        nlinarith [h302]
      linarith
    -- final steps for `h4`
    nlinarith [h19, h31]
  exact ⟨h1, h2, h3, h4⟩