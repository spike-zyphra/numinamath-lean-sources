import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_294478 (f : ℝ → ℝ) (hf : f = λ x => 2 * sin x * cos x / (1 + sin x + cos x)) :
    IsGreatest (range f) (Real.sqrt 2 - 1) := by 
  constructor
  · -- Show that `sqrt(2) - 1` is in the range of f.
    use Real.pi / 4
    rw [hf]
    have h1 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
    have h2 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
    simp only [h1, h2]
    have h3 : (2 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) : ℝ) = 1 := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num : (2 : ℝ) ≥ (0 : ℝ))]
    have h4 : (1 + Real.sqrt 2 / 2 + Real.sqrt 2 / 2 : ℝ) = 1 + Real.sqrt 2 := by
      ring_nf
    field_simp [h3, h4]
    <;> nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num : (2 : ℝ) > (0 : ℝ)), Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num : (2 : ℝ) ≥ (0 : ℝ))]
  · -- Show that `sqrt(2) - 1` is the greatest value in the range.
    intro y 
    rintro ⟨x, hx⟩
    rw [hf] at hx
    simp at hx 
    by_cases h1 : 1 + sin x + cos x = 0 
    · -- Case where denominator is zero, so y = 0
      rw [show 2 * sin x * cos x / (1 + sin x + cos x) = 0 by 
        rw [h1]
        norm_num
      ] at hx
      have : y = 0 := by linarith 
      rw [this]
      have h4 : Real.sqrt 2 ≥ 1 := by
        have h5 : 1 < (Real.sqrt 2 : ℝ) := by
          rw [Real.lt_sqrt] <;> norm_num 
        linarith 
      linarith [h4]
    · -- Case where denominator is non-zero.
      by_cases h4 : 1 + sin x + cos x > 0 
      · -- Case where denominator is positive.
        have h1 : 2 * sin x * cos x = (sin x + cos x) ^ 2 - 1 := by
          have h2 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
          nlinarith [sq_nonneg (sin x - cos x), h2]
        have h2 : (sin x + cos x) ^ 2 ≤ 2 := by 
          have h3 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
          nlinarith [sq_nonneg (sin x - cos x), h3]
        have h3 : sin x + cos x ≤ Real.sqrt 2 := by 
          have h4 : (sin x + cos x) ^ 2 ≤ (2 : ℝ) := h2
          have h5 : Real.sqrt ((sin x + cos x) ^ 2) ≤ Real.sqrt (2 : ℝ) := by
            apply Real.sqrt_le_sqrt 
            linarith 
          have h6 : Real.sqrt ((sin x + cos x) ^ 2) = |sin x + cos x| := by
            rw [Real.sqrt_sq_eq_abs]
          rw [h6] at h5
          cases abs_cases (sin x + cos x) with
          | inl h =>
            nlinarith
          | inr h =>
            nlinarith 
        have h10 : (2 * sin x * cos x) / (1 + sin x + cos x) ≤ Real.sqrt 2 - 1 := by
          have h8 : (2 * sin x * cos x) ≤ (Real.sqrt 2 - 1) * (1 + sin x + cos x) := by
            nlinarith [sq_nonneg (sin x + cos x - Real.sqrt 2), h3, Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num : (2 : ℝ) ≥ (0 : ℝ)), sq_nonneg (sin x - cos x)]
          apply (div_le_iff₀ h4).mpr 
          linarith 
        linarith [h10, hx]
      · -- Case where denominator is ≤ 0 and non-zero (so < 0).
        have h5 : 1 + sin x + cos x < (0 : ℝ) := by 
          by_contra h 
          push_neg at h 
          have h6 : 1 + sin x + cos x = (0 : ℝ) := by 
            nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (sin x + cos x), sq_nonneg (sin x - cos x)]
          tauto 
        have hx1 : (2 * sin x * cos x) / (1 + sin x + cos x) ≤ Real.sqrt 2 - 1 := by 
          have h7 : 2 * sin x * cos x ≥ (Real.sqrt 2 - 1) * (1 + sin x + cos x) := by
            nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num : (2 : ℝ) ≥ (0 : ℝ)), sq_nonneg (sin x + cos x + 1), sq_nonneg (sin x - cos x), sq_nonneg (sin x + cos x - Real.sqrt 2), Real.sin_sq_add_cos_sq x, sq_nonneg (sin x + cos x - 0)]
          apply (div_le_iff_of_neg' (by linarith)).mpr 
          linarith 
        linarith [hx1, hx]