import Mathlib

open Real Set
open scoped Real

theorem algebra_183076 (f : ℝ → ℝ) (hf : f = λ x => (sin x + 1) * (cos x + 1) / (sin x * cos x)) :
    IsLeast {x | ∃ t ∈ Ioo 0 (π/2), f t = x} (3 + 2 * sqrt 2) := by 
  constructor 
  · -- Show that 3 + 2 * sqrt 2 is in the set.
    use Real.pi / 4
    constructor
    · -- Show that π/4 is in the interval (0, π/2)
      exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    · -- Show that f(π/4) = 3 + 2 * sqrt 2
      have h1 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
      have h2 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
      rw [hf]
      simp only [h1, h2]
      field_simp
      ring_nf
      rw [Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)]
      ring 
  · -- Show that 3 + 2 * sqrt 2 is the least value in the set.
    intro x hx
    rcases hx with ⟨t, ht, rfl⟩
    rcases ht with ⟨ht1, ht2⟩
    rw [hf]
    have ht3 : 0 < t := ht1
    have ht4 : t < Real.pi / 2 := ht2
    have ht5 : 0 < sin t := by
      apply sin_pos_of_pos_of_lt_pi
      linarith 
      linarith 
    have ht6 : 0 < cos t := by 
      have ht7 : cos t > 0 := by
        apply cos_pos_of_mem_Ioo
        constructor 
        linarith 
        linarith 
      linarith 
    have ht7 : sin t * cos t > 0 := mul_pos ht5 ht6
    have hfx : (sin t + 1) * (cos t + 1) / (sin t * cos t) ≥ 3 + 2 * Real.sqrt 2 := by
      have hfx2 : (sin t + 1) * (cos t + 1) / (sin t * cos t) - (3 + 2 * Real.sqrt 2) ≥ 0 := by 
        have h1 : 0 < sin t * cos t := ht7 
        have h2 : (sin t + 1) * (cos t + 1) / (sin t * cos t) - (3 + 2 * Real.sqrt 2) = ((sin t + 1) * (cos t + 1) - (3 + 2 * Real.sqrt 2) * (sin t * cos t)) / (sin t * cos t) := by 
          field_simp 
          <;> ring 
        rw [h2] at *
        apply div_nonneg 
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), sq_nonneg (sin t - Real.sqrt 2 / 2), sq_nonneg (cos t - Real.sqrt 2 / 2), sq_nonneg (sin t - cos t), sq_nonneg ((sin t + cos t) - Real.sqrt 2), Real.sin_sq_add_cos_sq t, sq_nonneg (sin t * cos t - 1 / 2), mul_pos ht5 ht6, Real.sqrt_nonneg 2, sq_nonneg (sin t - cos t)]
        all_goals linarith 
      linarith 
    simpa using hfx