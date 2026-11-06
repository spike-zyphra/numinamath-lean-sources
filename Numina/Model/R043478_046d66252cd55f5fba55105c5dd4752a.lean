import Mathlib

open Real Set
open scoped Real

theorem algebra_138652 : IsGreatest {x | ∃ t : ℝ, x = cos t + sin t + cos t * sin t} (1/2 + sqrt 2) := by
  constructor
  · -- Show that 1/2 + sqrt 2 is achievable, using t = π/4
    use Real.pi / 4
    have h1 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
      rw [cos_pi_div_four]
    have h2 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
      rw [sin_pi_div_four]
    rw [h1, h2]
    have h3 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by
      exact Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
    nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), h3]
  · -- Show that 1/2 + sqrt 2 is the greatest such value
    intro x hx
    rcases hx with ⟨t, ht⟩
    have h1 : (cos t) ^ 2 + (sin t) ^ 2 = 1 := by
      exact Real.cos_sq_add_sin_sq t
    have h2 : cos t + sin t + cos t * sin t ≤ 1 / 2 + Real.sqrt 2 := by
      have h3 : cos t * sin t = ((cos t + sin t) ^ 2 - 1) / 2 := by
        have h4 : (cos t) ^ 2 + (sin t) ^ 2 = 1 := by
          linarith [h1]
        nlinarith [h4]
      have ht_eq : cos t + sin t + cos t * sin t = (1 / 2) * (cos t + sin t) ^ 2 + (cos t + sin t) - 1 / 2 := by
        linarith [h3]
      have h5 : cos t + sin t ≤ Real.sqrt 2 := by
        have h7 : (cos t + sin t) ^ 2 ≤ 2 := by
          nlinarith [sq_nonneg (cos t - sin t), sq_nonneg (cos t), sq_nonneg (sin t), Real.sin_sq_add_cos_sq t]
        have h6 : (cos t + sin t) ≤ Real.sqrt 2 := by
          apply Real.le_sqrt_of_sq_le
          linarith
        linarith
      rw [ht_eq]
      have h6 : (cos t + sin t) ^ 2 ≤ 2 := by
        nlinarith [sq_nonneg (cos t - sin t), sq_nonneg (cos t), sq_nonneg (sin t), Real.sin_sq_add_cos_sq t]
      nlinarith [sq_nonneg ( (cos t + sin t) - Real.sqrt 2 ), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg ((cos t + sin t) + 1), sq_nonneg (cos t - sin t)]
    linarith [ht, h2]