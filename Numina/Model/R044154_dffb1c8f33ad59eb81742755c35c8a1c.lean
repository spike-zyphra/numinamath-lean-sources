import Mathlib

open Real Set
open scoped Real

theorem algebra_144742 {a : ℝ} (ha : a ∈ Ioo (π/4) (π/2)) :
    (cos a)^(sin a) < (cos a)^(cos a) ∧ (cos a)^(cos a) < (sin a)^(cos a) := by 
  rcases ha with ⟨ha1, ha2⟩
  have h1 : cos a > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [ha1, ha2, Real.pi_gt_three]
    linarith [ha1, ha2, Real.pi_gt_three]
  have h2 : cos a < sin a := by
    have ha1' : a > π / 4 := by linarith
    have h3 : sin a - cos a > 0 := by
      have h5 : sin a - cos a = √2 * sin (a - π / 4) := by
        rw [sin_sub, sin_pi_div_four, cos_pi_div_four]
        ring_nf
        <;> field_simp
        <;> linarith [Real.sqrt_pos.mpr (show (0:ℝ) < (2:ℝ) by norm_num), mul_pos (Real.sqrt_pos.mpr (show (0:ℝ) < (2:ℝ) by norm_num)) (Real.sqrt_pos.mpr (show (0:ℝ) < (2:ℝ) by norm_num))]
      rw [h5]
      have h6 : sin (a - π / 4) > 0 := by
        apply sin_pos_of_pos_of_lt_pi
        linarith [ha1', Real.pi_gt_three]
        linarith [ha1', Real.pi_gt_three]
      have h7 : √2 > 0 := Real.sqrt_pos.mpr (by linarith)
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by linarith)]
    linarith
  have h5 : (cos a) ^ (sin a) < (cos a) ^ (cos a) := by
    have h2' : cos a < 1 := by
      have : cos a < cos (π / 4) := by 
        apply Real.cos_lt_cos_of_nonneg_of_le_pi
        all_goals linarith [ha1, ha2, Real.pi_gt_three]
      have hcos : cos (π / 4) = Real.sqrt 2 / 2 := by
        rw [cos_pi_div_four]
      rw [hcos] at this
      have h6 : Real.sqrt 2 < (2 : ℝ) := by
        rw [Real.sqrt_lt] <;> linarith [Real.pi_gt_three]
      have h7 : Real.sqrt 2 / 2 < (1 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by linarith)]
      linarith
    -- Since c > 0 and c < 1, so (cos a)^x is strictly decreasing monotonically
    have h2' : (cos a) ^ (sin a) < (cos a) ^ (cos a) := by
      have : sin a > cos a := by linarith
      have h3 : cos a > 0 := h1
      have h4 : cos a < 1 := by linarith [h2']
      have : (cos a) ^ (sin a) < (cos a) ^ (cos a) := by
        apply Real.rpow_lt_rpow_of_exponent_gt
        all_goals linarith
        all_goals nlinarith
      linarith
    linarith
  have h10 : (cos a) ^ (cos a) < (sin a) ^ (cos a) := by
    have h3 : cos a > 0 := h1
    have h4 : cos a < sin a := by linarith [h2]
    have h5 : cos a > 0 := h1
    have h6 : sin a > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [ha1, Real.pi_gt_three]
      linarith [ha1, Real.pi_gt_three]
    have : (cos a) ^ (cos a) < (sin a) ^ (cos a) := by
      apply Real.rpow_lt_rpow
      all_goals nlinarith
    linarith
  constructor
  · linarith [h5]
  · linarith [h10]