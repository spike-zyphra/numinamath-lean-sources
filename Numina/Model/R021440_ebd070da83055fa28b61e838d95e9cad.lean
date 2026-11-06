import Mathlib

theorem algebra_3603 (θ : ℝ) (hθ : 0 < θ ∧ θ < Real.pi / 2) (htan : Real.tan θ = 1 / Real.sqrt 3) :
    (1 + Real.cos θ) / (1 - Real.cos θ) - (1 - Real.cos θ) / (1 + Real.cos θ) = 8 * Real.sqrt 3 := by
  have h1 : θ = Real.arctan (Real.tan θ) := by
    rw [Real.arctan_tan]
    all_goals try linarith [hθ.1, hθ.2, Real.pi_pos]
  have h2 : θ = Real.arctan (1 / Real.sqrt 3) := by
    rw [h1, htan]
  have h3 : Real.arctan (1 / Real.sqrt 3) = Real.pi / 6 := by
    have h4 : Real.sin (Real.pi / 6) = 1 / 2 := Real.sin_pi_div_six
    have h5 : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := Real.cos_pi_div_six
    have htan : Real.tan (Real.pi / 6) = 1 / Real.sqrt 3 := by
      rw [Real.tan_eq_sin_div_cos, h4, h5]
      <;> field_simp <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    have h7 : Real.arctan (Real.tan (Real.pi / 6)) = Real.pi / 6 := by
      rw [Real.arctan_tan]
      all_goals try linarith [show 0 < Real.pi / 6 by linarith [Real.pi_pos], show Real.pi / 6 < Real.pi / 2 by linarith [Real.pi_pos]]
    rw [htan] at h7
    linarith
  have hθ2 : θ = Real.pi / 6 := by
    linarith [h2, h3]
  have hcos : Real.cos θ = Real.sqrt 3 / 2 := by
    rw [hθ2]
    exact Real.cos_pi_div_six
  rw [hcos]
  have h5 : 1 - Real.sqrt 3 / 2 ≠ 0 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have h6 : 1 + Real.sqrt 3 / 2 ≠ 0 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have h_eq : (1 + Real.sqrt 3 / 2) / (1 - Real.sqrt 3 / 2) - (1 - Real.sqrt 3 / 2) / (1 + Real.sqrt 3 / 2) = 8 * Real.sqrt 3 := by
    have h7 : (1 - Real.sqrt 3 / 2) = (2 - Real.sqrt 3) / 2 := by
      ring
    have h8 : (1 + Real.sqrt 3 / 2) = (2 + Real.sqrt 3) / 2 := by
      ring
    rw [h7, h8]
    field_simp [(show (2 - Real.sqrt 3) ≠ 0 by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    ), (show (2 + Real.sqrt 3) ≠ 0 by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    )
    ]
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), mul_pos (show (0 : ℝ) < (3 : ℝ) by norm_num) (show (0 : ℝ) < (3 : ℝ) by norm_num), sq_pos_of_pos (Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  linarith [h_eq]