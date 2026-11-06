import Mathlib

open Real Set
open scoped Real

theorem inequalities_107561 (α β γ : ℝ) (h : α + β + γ = π) :
  1 - sin (α / 2) ≥ 2 * sin (β / 2) * sin (γ / 2) := by
  have h1 : α = π - (β + γ) := by
    linarith 
  have h2 : sin (α / 2) = cos ((β + γ) / 2) := by
    rw [h1]
    have h3 : (π - (β + γ) : ℝ) / 2 = π / 2 - (β + γ) / 2 := by
      ring_nf
    rw [h3]
    rw [show sin (π / 2 - (β + γ) / 2) = cos ((β + γ) / 2) by 
      rw [sin_pi_div_two_sub]
    ]
  have h3 : cos ((β + γ) / 2) = cos (β / 2) * cos (γ / 2) - sin (β / 2) * sin (γ / 2) := by
    have h4 : (β + γ) / 2 = (β / 2) + (γ / 2) := by 
      ring_nf
    rw [h4]
    rw [cos_add]
    all_goals ring_nf
  rw [h2, h3]
  have h4 : cos (β / 2) * cos (γ / 2) + sin (β / 2) * sin (γ / 2) ≤ 1 := by 
    have h5 : cos (β / 2) * cos (γ / 2) + sin (β / 2) * sin (γ / 2) = cos ((β / 2) - (γ / 2)) := by
      rw [show (β / 2) - (γ / 2) = (β / 2) - (γ / 2) by ring_nf]
      rw [cos_sub]
      all_goals ring_nf
    have h6 : cos ((β / 2) - (γ / 2)) ≤ 1 := by 
      linarith [cos_le_one ((β / 2) - (γ / 2))]
    linarith [h5, h6]
  nlinarith [h4, sq_nonneg (cos (β / 2) - cos (γ / 2)), sq_nonneg (sin (β / 2) - sin (γ / 2)), Real.sin_sq_add_cos_sq (β / 2), Real.sin_sq_add_cos_sq (γ / 2)]