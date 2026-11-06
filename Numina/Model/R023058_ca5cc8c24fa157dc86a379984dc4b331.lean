import Mathlib

theorem calculus_16634 (x y : ℝ) (hy : y ∈ Set.Icc 0 (Real.pi / 2)) (h1 : x + Real.sin y = 2008) (h2 : x + 2008 * Real.cos y = 2007) :
    x + y = 2007 + Real.pi / 2 := by
  rcases hy with ⟨hy1, hy2⟩
  have h3 : Real.sin y - 2008 * Real.cos y = 1 := by 
    nlinarith 
  have h4 : Real.sin y ≤ 1 := by 
    apply Real.sin_le_one 
  have h6 : Real.sin y ≥ 0 := by 
    apply Real.sin_nonneg_of_nonneg_of_le_pi 
    linarith [Real.pi_gt_three, hy1]
    linarith [Real.pi_gt_three, hy2] 
  have h7 : Real.cos y ≥ 0 := by
    apply Real.cos_nonneg_of_mem_Icc 
    constructor 
    linarith [Real.pi_gt_three, hy1, hy2] 
    linarith [Real.pi_gt_three, hy1, hy2] 
  have h8 : Real.cos y = 0 := by 
    nlinarith [Real.sin_sq_add_cos_sq y, 
      sq_nonneg (Real.sin y - 1), 
      sq_nonneg (Real.cos y), 
      Real.sin_sq_add_cos_sq y, 
      mul_nonneg (show 0 ≤ (0 : ℝ) by linarith) (show 0 ≤ (0 : ℝ) by linarith)
    ] 
  have h9 : Real.sin y = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq y, h8, h4, h6]
  have h10 : y = Real.pi / 2 := by
    by_cases h : y < Real.pi / 2 
    · -- If y < π/2, then sin y < 1, which contradicts sin y = 1 
      have h13 : Real.sin y < 1 := by 
        have h14 : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two 
        have h15 : y < Real.pi / 2 := h 
        have h16 : Real.sin y < Real.sin (Real.pi / 2) := by 
          apply Real.sin_lt_sin_of_lt_of_le_pi_div_two 
          all_goals linarith [Real.pi_gt_three, h15] 
        linarith [h14, h16] 
      linarith [h9, h13]
    by_cases h : y > Real.pi / 2
    · -- Contradicts y ≤ π/2 
      linarith [h, hy2]
    linarith [Real.sin_pi_div_two, h9, h8, hy1, hy2]
  have h11 : x = 2007 := by 
    rw [show Real.sin y = 1 by linarith [h9]] at h1
    linarith 
  linarith [h11, h10]