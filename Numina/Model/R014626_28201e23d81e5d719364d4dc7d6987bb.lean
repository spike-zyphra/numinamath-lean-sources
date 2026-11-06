import Mathlib

open Real

theorem calculus_22202 : tan (2 * arctan (1 / 5) - π / 4) = -7 / 17 := by 
  have h1 : tan (2 * arctan (1 / 5)) = 5 / 12 := by
    have h2 : tan (2 * arctan (1 / 5)) = 2 * tan (arctan (1 / 5)) / (1 - tan (arctan (1 / 5)) ^ 2) := by 
      rw [tan_two_mul]
    have h3 : tan (arctan (1 / 5)) = 1 / 5 := by 
      rw [tan_arctan]
    rw [h2, h3]
    norm_num 
  have h2' : tan (π / 4) = 1 := by 
    exact tan_pi_div_four 
  have htan : tan (2 * arctan (1 / 5) - π / 4) = -7 / 17 := by
    have h3 : sin (2 * arctan (1 / 5) - π / 4) = sin (2 * arctan (1 / 5)) * cos (π / 4) - cos (2 * arctan (1 / 5)) * sin (π / 4) := by 
      rw [sin_sub]
    have h4 : cos (2 * arctan (1 / 5) - π / 4) = cos (2 * arctan (1 / 5)) * cos (π / 4) + sin (2 * arctan (1 / 5)) * sin (π / 4) := by 
      rw [cos_sub]
    have h5 : sin (2 * arctan (1 / 5)) = 5 / 13 := by 
      have h6 : sin (2 * arctan (1 / 5)) = 2 * sin (arctan (1 / 5)) * cos (arctan (1 / 5)) := by 
        rw [sin_two_mul]
      have h7 : sin (arctan (1 / 5)) = 1 / Real.sqrt 26 := by 
        have hx1 : sin (arctan (1 / 5)) = (1 / 5) / Real.sqrt (1 + (1 / 5: ℝ) ^ 2) := by 
          rw [sin_arctan]
        rw [hx1]
        have hx2 : (1: ℝ) + (1/5: ℝ)^2 = (26: ℝ) / 25 := by 
          norm_num 
        have hx3 : Real.sqrt ((26: ℝ) / 25) = Real.sqrt (26: ℝ) / 5 := by 
          rw [show (26: ℝ) / (25: ℝ) = (26: ℝ) / (5: ℝ)^2 by ring]
          field_simp [Real.sqrt_div]
        have hx4 : (1 / 5) / Real.sqrt ((1: ℝ) + (1/5: ℝ)^2) = (1/5) / (Real.sqrt (26: ℝ)/5) := by 
          rw [hx2, hx3]
        rw [hx4]
        field_simp
      have h8 : cos (arctan (1 / 5)) = 5 / Real.sqrt 26 := by 
        have hx1 : cos (arctan (1 / 5)) = 1 / Real.sqrt (1 + (1 / 5: ℝ) ^ 2) := by 
          rw [cos_arctan]
        rw [hx1]
        have hx2 : (1: ℝ) + (1/5: ℝ)^2 = (26: ℝ) / 25 := by 
          norm_num 
        have hx3 : Real.sqrt ((26: ℝ) / 25) = Real.sqrt (26: ℝ) / 5 := by 
          rw [show (26: ℝ) / (25: ℝ) = (26: ℝ) / (5: ℝ)^2 by ring]
          field_simp [Real.sqrt_div]
        have hx4 : 1 / Real.sqrt ((1: ℝ) + (1/5: ℝ)^2) = 1 / (Real.sqrt (26: ℝ) / 5) := by 
          rw [hx2, hx3]
        rw [hx4]
        field_simp
      rw [h6, h7, h8]
      field_simp 
      <;> norm_num 
    have h6 : cos (2 * arctan (1 / 5)) = 12 / 13 := by 
      have h7 : cos (2 * arctan (1 / 5)) = 2 * cos (arctan (1 / 5)) ^ 2 - 1 := by 
        rw [cos_two_mul]
      rw [h7, show cos (arctan (1/5)) = 5 / Real.sqrt 26 by
        have hx1 : cos (arctan (1 / 5)) = 1 / Real.sqrt (1 + (1 / 5: ℝ) ^ 2) := by 
          rw [cos_arctan]
        rw [hx1]
        have hx2 : (1: ℝ) + (1/5: ℝ)^2 = (26: ℝ) / 25 := by 
          norm_num 
        have hx3 : Real.sqrt ((26: ℝ) / 25) = Real.sqrt (26: ℝ) / 5 := by 
          rw [show (26: ℝ) / (25: ℝ) = (26: ℝ) / (5: ℝ)^2 by ring]
          field_simp [Real.sqrt_div]
        have hx4 : 1 / Real.sqrt ((1: ℝ) + (1/5: ℝ)^2) = 1 / (Real.sqrt (26: ℝ) / 5) := by 
          rw [hx2, hx3]
        rw [hx4]
        field_simp
      ]
      field_simp 
      <;> norm_num 
    have h7' : sin (π / 4) = Real.sqrt 2 / 2 := by 
      rw [sin_pi_div_four]
    have h8' : cos (π / 4) = Real.sqrt 2 / 2 := by 
      rw [cos_pi_div_four]
    have htan' : tan (2 * arctan (1 / 5) - π / 4) = 
      sin (2 * arctan (1 / 5) - π / 4) / cos (2 * arctan (1 / 5) - π / 4) := by 
      rw [tan_eq_sin_div_cos]
    rw [htan']
    rw [h3, h4]
    rw [h5, h6, h7', h8']
    field_simp
    <;> ring 
  exact htan