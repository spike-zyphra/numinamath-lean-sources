import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_138711 : IsLeast {x | ∃ t : ℝ, x = sin (2 * t) - (sin t + cos t) + 1} (-1 / 4) := by
  constructor
  · -- Show that -1/4 is in the set by choosing a particular t
    use Real.arcsin ((1 - Real.sqrt 7) / 4)
    have h2 : sin (2 * (Real.arcsin ((1 - Real.sqrt 7) / 4))) = 2 * sin (Real.arcsin ((1 - Real.sqrt 7) / 4)) * cos (Real.arcsin ((1 - Real.sqrt 7) / 4)) := by
      rw [sin_two_mul]
    have h3 : sin (Real.arcsin ((1 - Real.sqrt 7) / 4)) = (1 - Real.sqrt 7) / 4 := by
      apply Real.sin_arcsin
      · -- Show that (1 - Real.sqrt 7) / 4 ≥ -1
        nlinarith [Real.sqrt_pos.mpr (show (7 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
      · -- Show that (1 - Real.sqrt 7) / 4 ≤ 1
        nlinarith [Real.sqrt_pos.mpr (show (7 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
    have h4 : cos (Real.arcsin ((1 - Real.sqrt 7) / 4)) = (1 + Real.sqrt 7) / 4 := by
      have h5 : cos (Real.arcsin ((1 - Real.sqrt 7) / 4)) = Real.sqrt (1 - ((1 - Real.sqrt 7) / 4) ^ 2) := by
        rw [Real.cos_arcsin]
        <;> ring_nf <;> norm_num
        <;> ring
      rw [h5]
      have h6 : Real.sqrt (1 - ((1 - Real.sqrt 7) / 4) ^ 2) = (1 + Real.sqrt 7) / 4 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sqrt_pos.mpr (show (7 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
      exact h6
    rw [h2, h3, h4]
    nlinarith [Real.sqrt_pos.mpr (show (7 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
  · -- Show that -1/4 is indeed the least element
    intro x hx
    rcases hx with ⟨t, ht⟩
    have h5 : sin (2 * t) = 2 * sin t * cos t := by
      rw [sin_two_mul]
      <;> ring_nf <;> norm_num
    rw [h5] at ht
    nlinarith [sq_nonneg (sin t + cos t - 1 / 2), sq_nonneg (sin t - cos t), Real.sin_sq_add_cos_sq t, sq_nonneg (sin t), sq_nonneg (cos t)]