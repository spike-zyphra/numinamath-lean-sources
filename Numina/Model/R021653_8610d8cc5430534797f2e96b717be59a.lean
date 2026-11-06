import Mathlib

theorem algebra_217361 (x : ℝ) (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) (h : 2 * Real.sin x ^ 2 + Real.sin x - Real.sin (2 * x) = 3 * Real.cos x) :
    x = Real.pi / 3 := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := by
    rw [Real.sin_two_mul]
  have h2 : Real.sin x > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h3 : Real.cos x > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  rw [h1] at h
  have h5 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have h7 : Real.cos x = 1 / 2 := by
    have eq1 := h
    have eq2 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    nlinarith [sq_nonneg (Real.sin x - Real.sqrt 3 / 2), sq_nonneg (Real.cos x - 1 / 2), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have h8 : x = Real.arccos (1 / 2) := by
    have h9 : Real.cos x = 1 / 2 := h7
    have hx2' : x = Real.arccos (Real.cos x) := by 
      rw [Real.arccos_cos]
      all_goals linarith [Real.pi_pos]
    rw [hx2']
    rw [h9]
  have h9 : Real.arccos (1 / 2) = Real.pi / 3 := by
    have h10 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
    have h11 : Real.arccos (Real.cos (Real.pi / 3)) = Real.pi / 3 := by 
      rw [Real.arccos_cos]
      all_goals linarith [Real.pi_pos]
    rw [h10] at h11
    linarith
  rw [h9] at h8
  linarith