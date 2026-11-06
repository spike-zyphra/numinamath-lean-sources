import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_12545 :
  IsGreatest {x | ∃ t : ℝ, x = sqrt 3 / 2 * sin (t + π / 2) + cos (π / 6 - t)} (sqrt 13 / 2) := by
  constructor
  · -- Show that sqrt 13 / 2 is in the set
    use (Real.arctan (1 / (2 * sqrt 3)))
    have ht : sqrt 3 > 0 := by positivity
    have ht2 : (2 * sqrt 3) > 0 := by positivity
    have h1 : sin (Real.arctan (1 / (2 * sqrt 3))) = 1 / sqrt 13 := by
      rw [sin_arctan]
      field_simp
      <;> ring_nf <;> norm_num
      <;> ring_nf <;> norm_num
    have h2 : cos (Real.arctan (1 / (2 * sqrt 3))) = (2 * sqrt 3) / sqrt 13 := by
      rw [cos_arctan]
      field_simp
      <;> ring_nf <;> norm_num
      <;> ring_nf <;> norm_num
    have h3 : sin (Real.arctan (1 / (2 * sqrt 3)) + π / 2) = cos (Real.arctan (1 / (2 * sqrt 3))) := by
      rw [sin_add, sin_pi_div_two, cos_pi_div_two]
      ring
    have h4 : cos (π / 6 - Real.arctan (1 / (2 * sqrt 3))) = cos (π / 6) * cos (Real.arctan (1 / (2 * sqrt 3))) + sin (π / 6) * sin (Real.arctan (1 / (2 * sqrt 3))) := by
      rw [cos_sub]
    rw [h3, h4, Real.cos_pi_div_six, Real.sin_pi_div_six, h1, h2]
    have h5 : sqrt 3 > 0 := by positivity
    have h6 : sqrt 13 > 0 := by positivity
    field_simp
    <;> ring_nf <;> norm_num
    <;> ring_nf <;> norm_num
  · -- Show that sqrt 13 / 2 is the greatest
    intro x hx
    rcases hx with ⟨t, ht⟩
    have h1 : sqrt 3 / 2 * sin (t + π / 2) + cos (π / 6 - t) = Real.sqrt 3 * cos t + (1 / 2) * Real.sin t := by
      have h1 : sin (t + π / 2) = cos t := by
        rw [sin_add, sin_pi_div_two, cos_pi_div_two]
        ring
      have h2 : cos (π / 6 - t) = Real.cos (π / 6) * Real.cos t + Real.sin (π / 6) * Real.sin t := by
        rw [cos_sub]
      rw [h1, h2]
      rw [Real.cos_pi_div_six, Real.sin_pi_div_six]
      ring
    rw [h1] at ht
    have h2 : (Real.sqrt 3 * Real.cos t + (1 / 2) * Real.sin t) ^ 2 ≤ ( (Real.sqrt 3) ^ 2 + (1 / 2) ^ 2 ) * (Real.cos t ^ 2 + Real.sin t ^ 2 ) := by
      nlinarith [sq_nonneg (Real.sqrt 3 * Real.sin t - (1 / 2) * Real.cos t) ]
    have h3 : Real.cos t ^ 2 + Real.sin t ^ 2 = 1 := Real.cos_sq_add_sin_sq t
    have h4 : (Real.sqrt 3) ^ 2 + (1 / 2) ^ 2 = 13 / 4 := by
      nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    have h5 : (Real.sqrt 3 * Real.cos t + (1 / 2) * Real.sin t) ^ 2 ≤ 13 / 4 := by
      nlinarith [h2, h3, h4 ]
    have h6 : Real.sqrt 3 * Real.cos t + (1 / 2) * Real.sin t ≤ Real.sqrt 13 / 2 := by
      have h7 : Real.sqrt 13 / 2 ≥ 0 := by
        nlinarith [Real.sqrt_nonneg 13]
      nlinarith [sq_nonneg (Real.sqrt 3 * Real.cos t + (1 / 2) * Real.sin t - Real.sqrt 13 / 2), Real.sq_sqrt (show 0 ≤ (13 : ℝ) by norm_num), h5, Real.sqrt_nonneg 13]
    linarith [ht, h6]