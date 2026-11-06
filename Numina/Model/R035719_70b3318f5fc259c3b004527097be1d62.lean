import Mathlib

open Real Set
open scoped Real

theorem calculus_16672 {x : ℝ} (hx : x ∈ Icc 0 1) :
  arcsin x + arcsin (1 - x) = arccos x ↔ x = 0 ∨ x = 1 / 2 := by
  rcases hx with ⟨hx0, hx1⟩
  constructor
  · -- If arcsin x + arcsin (1 - x) = arccos x, then x = 0 or 1/2
    intro h
    have h1 : sin (arcsin x + arcsin (1 - x)) = sin (arccos x) := by
      rw [h]
    have h2 : sin (arcsin x + arcsin (1 - x)) = sin (arcsin x) * cos (arcsin (1 - x)) + cos (arcsin x) * sin (arcsin (1 - x)) := by
      rw [sin_add]
    have h3 : sin (arcsin x) = x := by 
      apply sin_arcsin
      linarith
      linarith
    have h4 : sin (arcsin (1 - x)) = 1 - x := by 
      apply sin_arcsin
      linarith
      linarith
    have h5 : cos (arcsin x) = Real.sqrt (1 - x ^ 2) := by 
      rw [cos_arcsin]
    have h6 : cos (arcsin (1 - x)) = Real.sqrt (1 - (1 - x) ^ 2) := by 
      rw [cos_arcsin]
    have h7 : sin (arccos x) = Real.sqrt (1 - x ^ 2) := by
      have h8 : sin (arccos x) = Real.sqrt (1 - x ^ 2) := by
        rw [sin_arccos]
        all_goals linarith
      exact h8
    rw [h2, h3, h4, h5, h6, h7] at h1
    have h8 : Real.sqrt (1 - (1 - x) ^ 2) = Real.sqrt (2 * x - x ^ 2) := by
      ring_nf
    have h9 : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x^2 := by
      rw [Real.sq_sqrt]
      nlinarith
    have h10 : Real.sqrt (1 - (1 - x) ^ 2) ^ 2 = 1 - (1 - x) ^ 2 := by
      rw [Real.sq_sqrt]
      nlinarith
    have h3 : x * Real.sqrt (2 * x - x^2) = x * Real.sqrt (1 - x^2) := by
      rw [h8] at h1
      nlinarith [Real.sqrt_nonneg (1 - x ^ 2), Real.sqrt_nonneg (2 * x - x ^ 2), 
        Real.sqrt_nonneg (1 - (1 - x) ^ 2), sq_nonneg (Real.sqrt (1 - x^2) - Real.sqrt (2 * x - x^2)), 
          Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 * x - x^2), Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - x ^ 2)]
    by_cases h4 : x > 0
    · -- x > 0 implies sqrt(2 * x - x ^ 2) = sqrt(1 - x^2)
      have h5 : Real.sqrt (2 * x - x^2) = Real.sqrt (1 - x^2) := by
        nlinarith
      have h6 : 2 * x - x^2 = 1 - x^2 := by
        calc
          2 * x - x^2 = (Real.sqrt (2 * x - x^2)) ^ 2 := by
            rw [Real.sq_sqrt]
            nlinarith
          _ = (Real.sqrt (1 - x^2)) ^ 2 := by
            rw [h5]
          _ = 1 - x^2 := by
            rw [Real.sq_sqrt]
            nlinarith
      have h7 : 2 * x = 1 := by
        nlinarith
      have h8 : x = 1 / 2 := by
        linarith
      right
      exact h8
    · -- Assume x ≤ 0
      have h9 : x = 0 := by
        linarith
      left
      exact h9
  · -- Prove the converse: x = 0 or 1/2 satisfies arcsin x + arcsin (1 - x) = arccos x
    rintro (h | h)
    · -- Case x = 0
      rw [h]
      norm_num [arcsin_zero, arcsin_one, arccos_zero]
    · -- Case x = 1/2
      rw [h]
      have ht1 : arcsin (1 / 2 : ℝ) = Real.pi / 6 := by 
        have h2 : sin (Real.pi / 6) = 1 / 2 := sin_pi_div_six
        rw [← h2]
        apply arcsin_sin
        all_goals linarith [Real.pi_pos]
      have ht2 : arcsin (1 - (1 / 2 : ℝ)) = Real.pi / 6 := by 
        have ht3 : (1 - (1 / 2 : ℝ) : ℝ) = 1 / 2 := by norm_num
        rw [ht3]
        have h2 : sin (Real.pi / 6) = 1 / 2 := sin_pi_div_six
        rw [← h2]
        apply arcsin_sin
        all_goals linarith [Real.pi_pos]
      have ht3 : arccos (1 / 2 : ℝ) = Real.pi / 3 := by 
        have h3 : cos (Real.pi / 3) = 1 / 2 := cos_pi_div_three
        rw [← h3]
        have h4 : arccos (cos (Real.pi / 3 : ℝ)) = Real.pi / 3 := by
          apply arccos_cos 
          all_goals linarith [Real.pi_pos]
        linarith
      linarith [ht1, ht2, ht3]