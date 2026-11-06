import Mathlib

open Real Set
open scoped Real

theorem algebra_293640 {f : ℝ → ℝ}
  (hf : f = λ x => (sqrt 2 * sin x + cos x) / (sin x + sqrt (1 - sin x))) :
  IsGreatest (image f (Icc 0 Real.pi)) (sqrt 2) := by

  constructor
  · -- Show sqrt 2 is in the image
    use Real.pi / 2
    constructor
    · -- Show that Real.pi / 2 is in [0, Real.pi]
      exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    · -- Show f (Real.pi / 2) = sqrt 2
      have h1 : sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
      have h2 : cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
      rw [hf]
      simp [h1, h2]
      all_goals norm_num [h1, h2, Real.sin_pi_div_two]
      all_goals linarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2]

  · -- Show sqrt 2 is the greatest in the image
    intro y hy
    rcases hy with ⟨x, hx, hfx⟩

    have h1 : 0 ≤ x := by
      have h1 : x ∈ Icc (0 : ℝ) Real.pi := by
        simpa using hx
      exact h1.1
    have h2 : x ≤ Real.pi := by
      have h1 : x ∈ Icc (0 : ℝ) Real.pi := by
        simpa using hx
      exact h1.2

    have h3 : sin x ≥ 0 := by
      apply sin_nonneg_of_nonneg_of_le_pi
      linarith [Real.pi_pos]
      linarith [Real.pi_pos]

    have h4 : sin x + sqrt (1 - sin x) > 0 := by
      by_cases h5 : sin x > 0
      · -- If sin x > 0, then the denominator is > 0.
        have h6 : sqrt (1 - sin x) ≥ 0 := Real.sqrt_nonneg (1 - sin x)
        nlinarith [show 0 ≤ (1 - sin x : ℝ) by nlinarith [sq_nonneg (sin x - 1), Real.sin_sq_add_cos_sq x]]
      · -- sin x = 0
        have h6 : sin x = 0 := by linarith
        have h7 : sqrt (1 - sin x) = 1 := by
          rw [h6]
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [h7]
        nlinarith

    have h5 : sqrt 2 * sin x + cos x ≤ sqrt 2 * (sin x + sqrt (1 - sin x)) := by
      have h7 : cos x ≤ Real.sqrt 2 * Real.sqrt (1 - sin x) := by
        have h6 : cos x ^ 2 = 1 - sin x ^ 2 := by
          have h7 : cos x ^ 2 + sin x ^ 2 = 1 := Real.cos_sq_add_sin_sq x
          linarith
        have h9 : cos x ^ 2 ≤ 2 * (1 - sin x) := by
          nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (cos x), sq_nonneg (1 - sin x), sq_nonneg (sin x - 1)]
        have h10 : cos x ≤ Real.sqrt (2 * (1 - sin x)) := by
          have h11 : cos x ^ 2 ≤ 2 * (1 - sin x) := h9
          have h12 : cos x ≤ Real.sqrt (2 * (1 - sin x)) := by
            apply Real.le_sqrt_of_sq_le
            linarith
          linarith
        have h11 : Real.sqrt (2 * (1 - sin x)) = Real.sqrt 2 * Real.sqrt (1 - sin x) := by
          rw [Real.sqrt_mul (by
            nlinarith [sq_nonneg (sin x - 1), Real.sin_sq_add_cos_sq x]
          )]
        nlinarith [h10, h11]

      nlinarith [h7, Real.sqrt_nonneg (2), Real.sqrt_nonneg (1 - sin x), Real.sin_sq_add_cos_sq x, sq_nonneg (sin x - 1), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (1 - sin x : ℝ) by
        nlinarith [sq_nonneg (sin x - 1), Real.sin_sq_add_cos_sq x]
      ), h3]

    have hfx_def : f x = (sqrt 2 * sin x + cos x) / (sin x + sqrt (1 - sin x)) := by
      rw [hf]

    rw [hfx_def] at hfx
    have h14 : (sqrt 2 * sin x + cos x) / (sin x + sqrt (1 - sin x)) ≤ sqrt 2 := by
      apply (div_le_iff₀ (by linarith)).mpr
      nlinarith [h5, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2, Real.sqrt_nonneg (1 - sin x), Real.sq_sqrt (show 0 ≤ (1 - sin x : ℝ) by
        nlinarith [sq_nonneg (sin x - 1), Real.sin_sq_add_cos_sq x]
      ), sq_nonneg (sin x - 1), h3, Real.sin_sq_add_cos_sq x]

    linarith [hfx, h14]