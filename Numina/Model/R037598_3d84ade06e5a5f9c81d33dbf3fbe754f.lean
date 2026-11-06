import Mathlib

open Real Set
open scoped Real

theorem inequalities_33409 (f : ℝ → ℝ)
  (h₀ : ∀ x ∈ Ioo 0 (π/2), f x = sin x ^ 3 / cos x + cos x ^ 3 / sin x) :
  IsGreatest {k | ∀ x ∈ Ioo 0 (π/2), f x ≥ k} 1 := by
  constructor
  · -- First part: Show 1 is a lower bound
    intro x hx
    rw [h₀ x hx]
    have h1 : 0 < x ∧ x < π / 2 := by 
      cases hx with
      | intro h2 h3 =>
        constructor <;> linarith [Real.pi_pos]
    have h2 : 0 < sin x := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [h1.1, Real.pi_pos]
      linarith [h1.2, Real.pi_pos]
    have h3 : 0 < cos x := by
      have hc : cos x > 0 := by
        apply cos_pos_of_mem_Ioo
        constructor <;> linarith [h1.2, Real.pi_pos]
      linarith
    have h4 : 0 < x ∧ x < π / 2 := h1
    have h5 : sin x ^ 3 / cos x + cos x ^ 3 / sin x ≥ 1 := by
      have h6 : sin x ^ 3 / cos x + cos x ^ 3 / sin x - 1 ≥ 0 := by
        have h7 : sin x * cos x > 0 := mul_pos h2 h3
        have h8 : (sin x ^ 3 / cos x + cos x ^ 3 / sin x) - 1 =
            (sin x ^ 4 + cos x ^ 4 - sin x * cos x) / (sin x * cos x) := by
          field_simp
          <;> nlinarith [sq_nonneg (sin x ^ 2 - cos x ^ 2), sq_nonneg (sin x - cos x), sq_nonneg (sin x * cos x - (1 : ℝ) / 2), Real.sin_sq_add_cos_sq x, sq_nonneg (sin x ^ 2 + cos x ^ 2 - 1), sq_nonneg (sin x * cos x - 1 / 2) ]
        rw [h8]
        have h9 : sin x ^ 4 + cos x ^ 4 - sin x * cos x ≥ 0 := by
          nlinarith [sq_nonneg (sin x ^ 2 - cos x ^ 2), sq_nonneg (sin x - cos x), sq_nonneg (sin x * cos x - (1 : ℝ) / 2), Real.sin_sq_add_cos_sq x, sq_nonneg (sin x), sq_nonneg (cos x), mul_pos h2 h3, sq_nonneg (sin x - cos x) ]
        apply div_nonneg
        linarith
        positivity
      linarith
    linarith
  · -- Show that k can't be greater
    intro k hk
    have h2 := hk (Real.pi / 4) (by
      constructor <;> linarith [Real.pi_pos]
    )
    have h1 : f (Real.pi / 4) = 1 := by
      rw [h₀ (Real.pi / 4) (by
        constructor <;> linarith [Real.pi_pos]
      )]
      have h3 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
        rw [sin_pi_div_four]
      have h4 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
        rw [cos_pi_div_four]
      rw [h3, h4]
      field_simp
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)]
    linarith [h1, h2]