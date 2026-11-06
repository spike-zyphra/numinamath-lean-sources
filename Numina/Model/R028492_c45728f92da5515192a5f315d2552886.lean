import Mathlib

theorem algebra_143766 (θ : ℝ) : Real.sin θ * Real.sin (Real.pi / 3 - θ) * Real.sin (Real.pi / 3 + θ) =
    (1 / 4) * Real.sin (3 * θ) := by

  have h1 : Real.sin (Real.pi / 3 - θ) = Real.sin (Real.pi / 3) * Real.cos θ - Real.cos (Real.pi / 3) * Real.sin θ := by
    rw [Real.sin_sub]

  have h2 : Real.sin (Real.pi / 3 + θ) = Real.sin (Real.pi / 3) * Real.cos θ + Real.cos (Real.pi / 3) * Real.sin θ := by 
    rw [Real.sin_add]

  have h3 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
  have h4 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three

  rw [h1, h2, h3, h4]

  have h5 : Real.sin (3 * θ) = 3 * Real.sin θ - 4 * Real.sin θ ^ 3 := by 
    rw [Real.sin_three_mul]

  rw [h5]

  have eq1 : Real.sin θ * ((Real.sqrt 3 / 2) * Real.cos θ - (1 / 2) * Real.sin θ) * ((Real.sqrt 3 / 2) * Real.cos θ + (1 / 2) * Real.sin θ) = (3 / 4) * Real.sin θ * Real.cos θ ^ 2 - (1 / 4) * Real.sin θ ^ 3 := by
    have h51 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
    calc 
      Real.sin θ * ((Real.sqrt 3 / 2) * Real.cos θ - (1 / 2) * Real.sin θ) * ((Real.sqrt 3 / 2) * Real.cos θ + (1 / 2) * Real.sin θ)
          = Real.sin θ * (((Real.sqrt 3 / 2) * Real.cos θ) ^ 2 - ((1 / 2) * Real.sin θ) ^ 2) := by ring
      _ = Real.sin θ * (( ( (Real.sqrt 3) ^ 2 / 4 ) * Real.cos θ ^ 2 ) - ( ( (1 : ℝ) / 4 ) * Real.sin θ ^ 2 )) := by
        ring_nf
      _ = Real.sin θ * (( (3 / 4 ) * Real.cos θ ^ 2 ) - ( (1 / 4 ) * Real.sin θ ^ 2 )) := by 
        rw [h51]
        all_goals norm_num 
      _ = (3 / 4) * Real.sin θ * Real.cos θ ^ 2 - (1 / 4) * Real.sin θ ^ 3 := by 
        ring_nf

  rw [eq1]

  have h6 : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
    have h7 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
    linarith 

  have h7 : (3 / 4) * Real.sin θ * Real.cos θ ^ 2 - (1 / 4) * Real.sin θ ^ 3 = (1 / 4) * (3 * Real.sin θ - 4 * Real.sin θ ^ 3) := by
    rw [show Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 by linarith [show Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 by exact Real.sin_sq_add_cos_sq θ] ]
    ring_nf

  linarith [h7]