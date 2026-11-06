import Mathlib

open Real Set
open scoped Real

theorem calculus_316798 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = (sin x - 1) / sqrt (3 - 2 * cos x - 2 * sin x)) :
  ∀ x ∈ Icc 0 (2 * π), f x ∈ Icc (-1) 0 := by
  intros x hx
  rcases hx with ⟨hx0, hx1⟩
  have hfx : f x = (sin x - 1) / sqrt (3 - 2 * cos x - 2 * sin x) := by
    apply h₀
  rw [hfx]
  have h1 : sin x ≤ (1 : ℝ) := by
    apply sin_le_one
  have h2 : sin x - 1 ≤ (0 : ℝ) := by
    linarith [h1]
  have h3 : sqrt (3 - 2 * cos x - 2 * sin x) ≥ 0 := by
    apply Real.sqrt_nonneg
  have h4 : (sin x - 1) / sqrt (3 - 2 * cos x - 2 * sin x) ≤ (0 : ℝ) := by
    apply div_nonpos_of_nonpos_of_nonneg
    linarith [h2]
    all_goals try { linarith [Real.sqrt_nonneg (3 - 2 * cos x - 2 * sin x), hfx] }
    all_goals try { 
      nlinarith [Real.sqrt_nonneg (3 - 2 * cos x - 2 * sin x), Real.sq_sqrt (show (0 : ℝ) ≤ (3 - 2 * cos x - 2 * sin x : ℝ) by nlinarith [sq_nonneg (sin x), sq_nonneg (cos x), Real.sin_sq_add_cos_sq x] : (0 : ℝ) ≤ (3 - 2 * cos x - 2 * sin x : ℝ)), sq_nonneg (sin x), sq_nonneg (cos x), Real.sin_sq_add_cos_sq x]
    }
  have h7 : -1 ≤ (sin x - 1) / sqrt (3 - 2 * cos x - 2 * sin x) := by
    have h11 : sqrt (3 - 2 * cos x - 2 * sin x) > 0 := by
      apply Real.sqrt_pos.2
      nlinarith [sq_nonneg (sin x - 1), sq_nonneg (cos x - sin x), sq_nonneg (cos x + sin x - Real.sqrt 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (0 : ℝ) ≤ 2), Real.sin_sq_add_cos_sq x]
    have h15 : (sin x - 1) / sqrt (3 - 2 * cos x - 2 * sin x) ≥ -1 := by
      have h16 : (sin x - 1) / sqrt (3 - 2 * cos x - 2 * sin x) ≥ -1 := by
        have h17 : sqrt (3 - 2 * cos x - 2 * sin x) > 0 := h11
        have h18 : sin x - 1 ≥ - sqrt (3 - 2 * cos x - 2 * sin x) := by
          have h19 : sin x - 1 ≥ - sqrt (3 - 2 * cos x - 2 * sin x) := by
            have h20 : (1 - sin x) ^ 2 ≤ (3 - 2 * cos x - 2 * sin x : ℝ) := by
              nlinarith [sq_nonneg (sin x - 1), sq_nonneg (cos x - 1), Real.sin_sq_add_cos_sq x, sq_nonneg (cos x - sin x), sq_nonneg (cos x + sin x - Real.sqrt 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (0 : ℝ) ≤ 2)]
            have h21 : sqrt (3 - 2 * cos x - 2 * sin x) ≥ 0 := by positivity
            have h22 : (1 - sin x : ℝ) ≥ 0 := by nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (sin x - 1), sq_nonneg (cos x - 1)]
            have h23 : (sin x - 1 : ℝ) ≥ - sqrt (3 - 2 * cos x - 2 * sin x) := by
              nlinarith [Real.sqrt_nonneg (3 - 2 * cos x - 2 * sin x), Real.sq_sqrt (show (0 : ℝ) ≤ (3 - 2 * cos x - 2 * sin x : ℝ) by nlinarith [sq_nonneg (sin x - 1), sq_nonneg (cos x - sin x), sq_nonneg (cos x + sin x - Real.sqrt 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (0 : ℝ) ≤ 2), Real.sin_sq_add_cos_sq x] : (0 : ℝ) ≤ (3 - 2 * cos x - 2 * sin x : ℝ)), h20, h22]
            linarith
          linarith [h19]
        have h19 : (sin x - 1) / sqrt (3 - 2 * cos x - 2 * sin x) ≥ -1 := by
          apply (le_div_iff₀ (by linarith : sqrt (3 - 2 * cos x - 2 * sin x) > 0)).mpr
          nlinarith [h18, Real.sqrt_nonneg (3 - 2 * cos x - 2 * sin x)]
        linarith [h19]
      linarith [h16]
    linarith [h15]
  constructor
  · linarith [h7]
  · linarith [h4, h7]