import Mathlib

open Real Set
open scoped Real

theorem algebra_133176 (f : ℝ → ℝ) (hf : f = λ x => sin x ^ 4 + 2 * sin x * cos x + cos x ^ 4) :
    IsLeast (range f) (-1 / 2) := by
  constructor
  · -- Show that -1/2 is in the range
    use (3 * Real.pi / 4)
    rw [hf]
    have h1 : sin (3 * Real.pi / 4) = Real.sqrt 2 / 2 := by 
      have h1 : sin (3 * Real.pi / 4) = sin (Real.pi - (Real.pi / 4)) := by 
        ring_nf
      rw [h1]
      rw [sin_pi_sub]
      have h2 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by 
        exact sin_pi_div_four
      rw [h2]
    have h2 : cos (3 * Real.pi / 4) = -Real.sqrt 2 / 2 := by 
      have h3 : cos (3 * Real.pi / 4) = cos (Real.pi - (Real.pi / 4)) := by 
        ring_nf
      rw [h3]
      rw [cos_pi_sub]
      have h4 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by 
        exact cos_pi_div_four
      rw [h4]
      all_goals ring
    simp only [h1, h2]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  · -- Show that -1/2 is the least in the range
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [hf] at hx
    have h_eq1 : sin x ^ 4 + 2 * sin x * cos x + cos x ^ 4 = y := by 
      simp at hx ⊢
      linarith
    nlinarith [sq_nonneg (sin x ^ 2 - cos x ^ 2), sq_nonneg (sin x - cos x), sq_nonneg (sin x + cos x), sq_nonneg (sin x * cos x + 1 / 2), Real.sin_sq_add_cos_sq x, sq_nonneg (sin x - (-cos x)), sq_nonneg (cos x - (-sin x)), sq_nonneg ((sin x - Real.sqrt 2 / 2) + (cos x + Real.sqrt 2 / 2)), sq_nonneg ((sin x + Real.sqrt 2 / 2) - (cos x - Real.sqrt 2 / 2)), Real.sin_sq_add_cos_sq x]