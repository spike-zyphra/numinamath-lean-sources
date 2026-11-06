import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_109959 {f : ℝ → ℝ} (hf : f = λ x => sin x / (2 + cos x)) :
    ¬ ∀ x, f x ≥ (1 / 3) * sin x := by
  intro h
  have h1 := h (3 * (Real.pi / 2))
  have h3 : sin (3 * (Real.pi / 2)) = -1 := by 
    have h3 : sin (3 * (Real.pi / 2)) = sin (Real.pi + (Real.pi / 2)) := by 
      ring_nf 
    rw [h3]
    rw [sin_add]
    simp [sin_pi, cos_pi, sin_pi_div_two, cos_pi_div_two]
    <;> try linarith
  have h4 : f (3 * (Real.pi / 2)) = -1 / 2 := by 
    rw [hf]
    have h3' : sin (3 * (Real.pi / 2)) = -1 := h3
    have h4' : cos (3 * (Real.pi / 2)) = 0 := by 
      have h4 : cos (3 * (Real.pi / 2)) = cos (Real.pi + (Real.pi / 2)) := by 
        ring_nf 
      rw [h4]
      rw [cos_add]
      simp [sin_pi, cos_pi, sin_pi_div_two, cos_pi_div_two]
      <;> try linarith 
    simp [h3', h4']
    <;> try norm_num 
  have h5 : (1 / 3) * sin (3 * (Real.pi / 2)) = -1 / 3 := by 
    rw [h3]
    norm_num 
  linarith [h1, h4, h5]