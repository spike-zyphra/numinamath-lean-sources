import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_142687 {f g h : ℝ → ℝ}
  (hf : f = λ φ => cos (2 * φ)) (hg : g = λ φ => 4 * sin φ) (hh : h = λ φ => 2 * sin φ)
  (h1 : ∀ φ, f φ > 0) (h2 : ∀ φ, g φ > 0) (h3 : ∀ φ, h φ > 0) :
  ∫ φ in (0)..(π / 2), f φ = π / 4 ∧
  ∫ φ in (0)..(π / 2), g φ - ∫ φ in (0)..(π / 2), h φ = 3 * π ∧
  ∫ φ in (0)..(π / 2), sin (3 * φ) = π := by 
  have h4 := h1 (Real.pi / 3) 
  simp [hf] at h4
  have h5 : cos (2 * (Real.pi / 3)) = -1 / 2 := by
    have h8 : cos (2 * (Real.pi / 3)) = -1 / 2 := by 
      have h9 : cos (2 * (Real.pi / 3)) = cos (2 * Real.pi / 3) := by ring
      rw [h9]
      have h10 : cos (2 * Real.pi / 3) = cos (Real.pi - (Real.pi / 3)) := by
        ring_nf  
      rw [h10]
      have h11 : cos (Real.pi - (Real.pi / 3)) = - cos (Real.pi / 3) := by 
        rw [cos_pi_sub]
      rw [h11]
      rw [cos_pi_div_three]
      all_goals linarith
    linarith
  rw [h5] at h4 
  linarith