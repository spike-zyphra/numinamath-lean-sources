import Mathlib

open Real Set
open scoped Real

theorem algebra_281633 (f : ℝ → ℝ) (hf : f = λ x => sin x * sin (2 * x)) :
    IsGreatest (image f (Ioo 0 (π / 2))) (4 * sqrt 3 / 9) := by 
  constructor 
  · -- Show 4 * sqrt 3 / 9 is in the image of f over (0, π / 2)
    use Real.arccos (Real.sqrt 3 / 3)
    constructor
    · -- Show Real.arccos (sqrt 3 / 3) is in the interval (0, π / 2)
      have h1 : Real.sqrt 3 / 3 > 0 := by
        positivity
      have h2 : Real.sqrt 3 / 3 < (1 : ℝ) := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      have h3 : Real.arccos (Real.sqrt 3 / 3) > 0 := by
        apply Real.arccos_pos.mpr
        nlinarith [h1, h2]
      have h4 : Real.arccos (Real.sqrt 3 / 3) < Real.pi / 2 := by
        apply (Real.arccos_lt_pi_div_two).mpr
        norm_num
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.pi_pos]
      exact ⟨h3, h4⟩
    · -- Show f (arccos (sqrt 3 / 3)) = 4 * sqrt 3 / 9
      have h5 : sin (Real.arccos (Real.sqrt 3 / 3)) = Real.sqrt (1 - (Real.sqrt 3 / 3)^2) := by
        rw [sin_arccos]
      have h6 : sin (Real.arccos (Real.sqrt 3 / 3)) = Real.sqrt 6 / 3 := by
        rw [h5]
        have h7 : (1 - (Real.sqrt 3 / 3)^2 : ℝ) = (6 : ℝ) / 9 := by
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
        rw [h7]
        have h8 : Real.sqrt ((6 / 9 : ℝ)) = Real.sqrt 6 / 3 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          <;> ring_nf <;> norm_num
        rw [h8]
      have h6' : sin (2 * Real.arccos (Real.sqrt 3 / 3)) = 2 * (Real.sqrt 6 / 3) * (Real.sqrt 3 / 3) := by
        rw [sin_two_mul]
        rw [h6]
        have h9 : cos (Real.arccos (Real.sqrt 3 / 3)) = Real.sqrt 3 / 3 := by
          apply Real.cos_arccos
          all_goals
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
        rw [h9]
      rw [hf]
      simp [h6', h6]
      have h10 : Real.sqrt 6 * Real.sqrt 3 = 3 * Real.sqrt 2 := by
        calc
          Real.sqrt 6 * Real.sqrt 3 = Real.sqrt (6 * 3) := by rw [Real.sqrt_mul (by norm_num)]
          _ = Real.sqrt 18 := by norm_num
          _ = Real.sqrt (9 * 2) := by norm_num
          _ = Real.sqrt 9 * Real.sqrt 2 := by rw [Real.sqrt_mul (by norm_num)]
          _ = (3 : ℝ) * Real.sqrt 2 := by
            have h10 : Real.sqrt (9 : ℝ) = (3 : ℝ) := by
              rw [Real.sqrt_eq_cases]
              all_goals norm_num
            rw [h10]
      field_simp [h10]
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.pi_pos]
  · -- Show that 4 * sqrt 3 / 9 is the greatest element in the image
    intro y hy
    rcases hy with ⟨x, hx, hfx⟩
    rcases hx with ⟨hx1, hx2⟩
    rw [hf] at hfx
    simp at hfx
    have h2x1 : sin x > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [Real.pi_gt_three, hx1, hx2]
      linarith [Real.pi_gt_three, hx1, hx2]
    have h2x2 : cos x > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor <;> linarith [Real.pi_gt_three, hx1, hx2]
    have h3 : sin (2 * x) = 2 * sin x * cos x := by
      rw [sin_two_mul]
    rw [h3] at hfx
    have h4 : sin x * (2 * sin x * cos x) = 2 * (sin x) ^ 2 * cos x := by ring
    rw [h4] at hfx
    nlinarith [sq_nonneg (sin x ^ 2 - 2 / 3), sq_nonneg (cos x ^ 2 - 1 / 3), sq_nonneg (sin x - Real.sqrt 6 / 3), sq_nonneg (cos x - Real.sqrt 3 / 3), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (sin x), sq_nonneg (cos x), Real.sin_sq_add_cos_sq x, sq_nonneg (sin x ^ 2 - 2 / 3), sq_nonneg (cos x ^ 2 - 1 / 3), mul_pos h2x1 (show (0 : ℝ) < cos x by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]