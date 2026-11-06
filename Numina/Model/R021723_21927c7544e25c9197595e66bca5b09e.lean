import Mathlib

open Real Set
open scoped Real

/- Let $x$ be an acute angle, then the maximum value of the function $y=\sin x\sin 2x$ is ___          ___. -/
theorem algebra_12339 (f : ℝ → ℝ) (hf : f = λ x => sin x * sin (2 * x)) :
    IsGreatest (image f (Ioo 0 (π / 2))) (4 / 9 * sqrt 3) := by
  constructor
  · -- Show that 4/9 * sqrt 3 is in the image of f over (0, π/2)
    use arcsin (Real.sqrt (2 / 3))
    constructor
    · -- Show that arcsin (Real.sqrt (2 / 3)) is in (0, π/2)
      have h1 : 0 < Real.sqrt (2 / 3) := by
        apply Real.sqrt_pos.2
        norm_num
      have h2 : Real.sqrt (2 / 3) < 1 := by
        nlinarith [Real.sqrt_nonneg (2 / 3), Real.sq_sqrt (show 0 ≤ (2 / 3 : ℝ) by norm_num)]
      have h3 : arcsin (Real.sqrt (2 / 3)) > 0 := by
        apply arcsin_pos.mpr
        linarith [h1]
      have h4 : arcsin (Real.sqrt (2 / 3)) < Real.pi / 2 := by
        apply arcsin_lt_pi_div_two.mpr
        linarith [show Real.sqrt (2 / 3) < 1 by linarith [Real.sqrt_nonneg (2/3), Real.sq_sqrt (show 0 ≤ (2 / 3 : ℝ) by norm_num)]]
      exact ⟨by linarith, by linarith⟩
    · -- Show that f (arcsin (Real.sqrt (2 / 3))) = 4 / 9 * Real.sqrt 3
      rw [hf]
      have h4 : sin (arcsin (Real.sqrt (2 / 3))) = Real.sqrt (2 / 3) := by
        apply sin_arcsin
        · -- Show sqrt (2 / 3) ≥ -1
          have h : Real.sqrt (2 / 3) ≥ 0 := Real.sqrt_nonneg (2 / 3)
          linarith
        · -- Show sqrt (2 / 3) ≤ 1
          have h1 : Real.sqrt (2 / 3) < 1 := by
            nlinarith [Real.sqrt_nonneg (2 / 3), Real.sq_sqrt (show 0 ≤ (2 / 3 : ℝ) by norm_num)]
          linarith
      have h5 : sin (2 * arcsin (Real.sqrt (2 / 3))) = 2 * Real.sqrt (2 / 3) * (Real.sqrt 3 / 3) := by
        have h6 : sin (2 * arcsin (Real.sqrt (2 / 3))) = 2 * sin (arcsin (Real.sqrt (2 / 3))) * cos (arcsin (Real.sqrt (2 / 3))) := by
          rw [sin_two_mul]
        have h7 : cos (arcsin (Real.sqrt (2 / 3))) = Real.sqrt 3 / 3 := by
          have h3 : cos (arcsin (Real.sqrt (2 / 3))) = Real.sqrt (1 - (Real.sqrt (2 / 3)) ^ 2) := by
            rw [cos_arcsin]
          have h4 : (Real.sqrt (2 / 3) : ℝ) ^ 2 = 2 / 3 := by
            rw [Real.sq_sqrt]
            linarith
          have h5 : (1 : ℝ) - (Real.sqrt (2 / 3) : ℝ) ^ 2 = 1 / 3 := by
            rw [h4]
            linarith
          have h8 : Real.sqrt (1 / 3) = Real.sqrt 3 / 3 := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
            <;> ring_nf <;> norm_num
          rw [h3, h5, h8]
          all_goals linarith
        rw [h6, h7, h4]
        all_goals nlinarith
      have hfx : (fun x => sin x * sin (2 * x)) (arcsin (Real.sqrt (2 / 3))) = 4 / 9 * Real.sqrt 3 := by
        simp only [h4, h5]
        have h2 : Real.sqrt (2 / 3) ^ 2 = (2/3) := by
          rw [Real.sq_sqrt]
          norm_num
        nlinarith [Real.sqrt_nonneg (2 / 3), Real.sqrt_nonneg 3, Real.sq_sqrt (show (2 / 3 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]
      simpa using hfx
  · -- Show that 4/9 * sqrt 3 is the greatest element in the image
    intro y hy
    rcases hy with ⟨x, hx, hfx⟩
    rw [hf] at hfx
    simp at hfx
    have hx1 : 0 < x := by
      have h : x ∈ Ioo (0 : ℝ) (Real.pi / 2) := by
        simpa using hx
      exact h.1
    have hx2 : x < Real.pi / 2 := by
      have h : x ∈ Ioo (0 : ℝ) (Real.pi / 2) := by
        simpa using hx
      exact h.2
    have h1 : sin x > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      · -- Show 0 < x < pi
        linarith [Real.pi_gt_three]
      · -- Show x < pi
        linarith [Real.pi_gt_three, hx2]
    have h2 : cos x > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      · -- Show -pi/2 < x
        linarith [Real.pi_pos, hx1]
      · -- Show x < pi/2
        linarith
    have h3 : sin (2 * x) = 2 * sin x * cos x := by
      rw [sin_two_mul]
    rw [h3] at hfx
    have h4 : (sin x) ^ 2 + (cos x) ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    nlinarith [sq_nonneg (sin x - Real.sqrt (2 / 3)), sq_nonneg (sin x + Real.sqrt (2 / 3)), sq_nonneg (cos x - Real.sqrt 3 / 3), Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < (2 / 3 : ℝ)), Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (show 0 ≤ (2 / 3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg (2 / 3), Real.sqrt_nonneg 3, mul_pos h1 h2, sq_nonneg (sin x ^ 2 - 2 / 3)]