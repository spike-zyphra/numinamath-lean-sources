import Mathlib

open Real Set
open scoped Real

theorem algebra_231983 (x : ℝ) (hx : x ∈ Ioo 0 (π/4)) (h : sin (π/4 - x) = 5/13) :
    cos (2*x)/cos (π/4 + x) = 24/13 := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : π/4 - x > 0 := by linarith [Real.pi_pos, hx1, hx2]
  have h2 : π/4 + x < π/2 := by linarith [Real.pi_pos, hx1, hx2]
  have h3 : cos (π/4 + x) = sin (π/4 - x) := by
    have h5 : π/4 + x = Real.pi/2 - (π/4 - x) := by 
      ring
    rw [h5]
    rw [cos_pi_div_two_sub]
  have h4 : cos (π/4 + x) = 5/13 := by
    rw [h3]
    linarith [h]
  have h5 : cos (π/4 - x) > 0 := by 
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith [Real.pi_pos, h1]
    · linarith [Real.pi_pos, h1]
  have h6 : cos (π/4 - x) = 12/13 := by 
    have h12 : cos (π/4 - x) ^ 2 + sin (π/4 - x) ^ 2 = 1 := Real.cos_sq_add_sin_sq (π/4 - x)
    rw [show sin (π/4 - x) = 5/13 by linarith [h]] at h12
    have h13 : cos (π/4 - x) ^ 2 = 144/169 := by
      linarith
    have h14 : cos (π/4 - x) > 0 := by 
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · linarith [Real.pi_pos, h1]
      · linarith [Real.pi_pos, h1]
    have h15 : cos (π/4 - x) = 12/13 := by 
      nlinarith 
    linarith [h15]
  have h9 : sin (π / 4 + x) > 0 := by 
    apply Real.sin_pos_of_pos_of_lt_pi
    all_goals linarith [Real.pi_pos, h2]
  have h10 : sin (π / 4 + x) ^ 2 + cos (π / 4 + x) ^ 2 = 1 := by 
    exact Real.sin_sq_add_cos_sq (π / 4 + x)
  have h11 : sin (π / 4 + x) = 12/13 := by 
    rw [show cos (π / 4 + x) = 5/13 by linarith [h4]] at h10
    have h15 : sin (π / 4 + x) ^ 2 = 144/169 := by 
      linarith 
    have h16 : sin (π / 4 + x) = 12/13 := by 
      nlinarith [h9]
    linarith [h16]
  have h8 : sin x = (7 * Real.sqrt 2) / 26 := by 
    have h5 : sin x = sin (π / 4 + x) * Real.sqrt 2 / 2 - cos (π / 4 + x) * Real.sqrt 2 / 2 := by
      have h6 : sin x = sin (π / 4 + x) * Real.sqrt 2 / 2 - cos (π / 4 + x) * Real.sqrt 2 / 2 := by 
        have h7 : sin x = sin ((π / 4 + x) - Real.pi / 4) := by 
          ring_nf
        rw [h7]
        rw [sin_sub, Real.sin_pi_div_four, Real.cos_pi_div_four]
        all_goals ring_nf
        all_goals linarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      linarith [h6]
    rw [h5]
    rw [h11, h4]
    field_simp
    ring_nf
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    all_goals linarith 
  have h12 : cos x = (17 * Real.sqrt 2) / 26 := by 
    have h5 : cos x = cos (π / 4 + x) * Real.sqrt 2 / 2 + sin (π / 4 + x) * Real.sqrt 2 / 2 := by 
      have h7 : cos x = cos ((π / 4 + x) - Real.pi / 4) := by 
        ring_nf
      rw [h7]
      rw [cos_sub, Real.sin_pi_div_four, Real.cos_pi_div_four]
      all_goals ring_nf
      all_goals linarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    rw [h5, h4, h11]
    field_simp
    ring_nf
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    all_goals linarith 
  have h2x_c : cos (2 * x) = 120 / 169 := by 
    have h15 : cos (2 * x) = 2 * cos x ^ 2 - 1 := by 
      rw [cos_two_mul]
    rw [h15, h12]
    ring_nf 
    <;> norm_num 
    all_goals ring_nf 
    all_goals norm_num 
    all_goals linarith 
  rw [h2x_c, h4]
  all_goals norm_num
  all_goals ring_nf
  all_goals linarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  all_goals norm_num [Real.sqrt_pos.mpr]
  all_goals linarith 
  all_goals norm_num 
  all_goals linarith 
  all_goals norm_num 
  all_goals nlinarith