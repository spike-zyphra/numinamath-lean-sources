import Mathlib

theorem algebra_148423 (α : ℝ) (hα : α = Real.pi / 4) :
    Real.sin (2 * α) / (1 + Real.tan α) + (Real.cos α + (Real.sin α) ^ 2) ^ 2 =
    (5 + 2 * Real.sqrt 2) / 4 := by
  rw [hα]
  have h1 : Real.sin (2 * (Real.pi / 4)) = 1 := by
    have h2 : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
    rw [h2]
    exact Real.sin_pi_div_two
  have h2 : Real.tan (Real.pi / 4) = 1 := by
    exact Real.tan_pi_div_four
  have h3 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
    exact Real.sin_pi_div_four
  have h4 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
    exact Real.cos_pi_div_four
  have h5 : Real.sin (2 * (Real.pi / 4)) / (1 + Real.tan (Real.pi / 4)) = 1 / 2 := by
    rw [h1, h2]
    all_goals norm_num
  have h6 : Real.cos (Real.pi / 4) + (Real.sin (Real.pi / 4)) ^ 2 = Real.sqrt 2 / 2 + 1 / 2 := by
    rw [h3, h4]
    have h7 : (Real.sqrt 2 / 2 : ℝ) ^ 2 = 1 / 2 := by
      calc
        (Real.sqrt 2 / 2 : ℝ) ^ 2 = (Real.sqrt 2 ^ 2) / 4 := by ring_nf
        _ = (2 : ℝ) / 4 := by rw [Real.sq_sqrt]; all_goals positivity
        _ = (1 : ℝ) / 2 := by norm_num
    nlinarith [h7]
  have h8 : (Real.cos (Real.pi / 4) + (Real.sin (Real.pi / 4)) ^ 2) ^ 2 = (Real.sqrt 2 / 2 + 1 / 2) ^ 2 := by
    rw [h6]
  have h9 : (Real.sqrt 2 / 2 + 1 / 2 : ℝ) ^ 2 = (3 + 2 * Real.sqrt 2) / 4 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  rw [h5, h8, h9]
  all_goals ring_nf <;> field_simp <;> ring_nf <;> norm_num
  <;> ring