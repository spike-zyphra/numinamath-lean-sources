import Mathlib

open Real Set
open scoped Real

lemma sin_add' : ∀ (x y : ℝ), sin x + sin y = 2 * sin ((x + y) / 2) * cos ((x - y) /2 ):= by 
  intro x y
  obtain h1 := sin_add ((x + y) / 2) ((x - y) / 2)
  obtain h2 := sin_sub ((x + y) / 2) ((x - y) / 2)
  ring_nf at h1 h2
  rw [h1, h2]
  ring_nf

theorem algebra_277953 (x α β γ : ℝ) (h1 : sin (α - β) ≠ 0) (h2 : sin (α - γ) ≠ 0) 
  (h3 : sin (β - γ) ≠ 0)
  :
  sin (x - β) * sin (x - γ) / (sin (α - β) * sin (α - γ)) +
  sin (x - γ) * sin (x - α) / (sin (β - γ) * sin (β - α)) +
  sin (x - α) * sin (x - β) / (sin (γ - α) * sin (γ - β)) = 1 := by

  have h6 : sin (β - α) = - sin (α - β) := by 
    rw [show β - α = - (α - β) by ring]
    rw [sin_neg]

  have h7 : sin (γ - α) = - sin (α - γ) := by
    rw [show γ - α = - (α - γ) by ring]
    rw [sin_neg]

  have h8 : sin (γ - β) = - sin (β - γ) := by 
    rw [show γ - β = - (β - γ) by ring]
    rw [sin_neg]

  have eq1 : sin (x - β) * sin (x - γ) / (sin (α - β) * sin (α - γ)) +
  sin (x - γ) * sin (x - α) / (sin (β - γ) * sin (β - α)) +
  sin (x - α) * sin (x - β) / (sin (γ - α) * sin (γ - β)) = 
  sin (x - β) * sin (x - γ) / (sin (α - β) * sin (α - γ)) +
  sin (x - γ) * sin (x - α) / (sin (β - γ) * (- sin (α - β)) ) +
  sin (x - α) * sin (x - β) / ( ( - sin (α - γ) ) * ( - sin (β - γ) ) ) := by 
    simp only [h6, h7, h8]

  rw [eq1] 
  have eq2 :  sin (x - β) * sin (x - γ) / (sin (α - β) * sin (α - γ)) +
  sin (x - γ) * sin (x - α) / (sin (β - γ) * (- sin (α - β)) ) +
  sin (x - α) * sin (x - β) / ( ( - sin (α - γ) ) * ( - sin (β - γ) ) ) =
  (sin (x - β) * sin (x - γ) * sin (β - γ) - sin (x - γ) * sin (x - α) * sin (α - γ) + sin (x - α) * sin (x - β) * sin (α - β)) / (sin (α - β) * sin (α - γ) * sin (β - γ)) := by 
    field_simp [(show sin (α - β) ≠ 0 by assumption), (show sin (α - γ) ≠ 0 by assumption), (show sin (β - γ) ≠ 0 by assumption)]
    ring
  rw [eq2]
  have eq3 : sin (x - β) * sin (x - γ) * sin (β - γ) - sin (x - γ) * sin (x - α) * sin (α - γ) + sin (x - α) * sin (x - β) * sin (α - β) = 
  sin (α - β) * sin (α - γ) * sin (β - γ) := by
    have eq4 : sin (x - β) = sin x * cos β - cos x * sin β := by 
      rw [sin_sub]

    have eq5 : sin (x - γ) = sin x * cos γ - cos x * sin γ := by 
      rw [sin_sub]

    have eq6 : sin (x - α) = sin x * cos α - cos x * sin α := by 
      rw [sin_sub]

    have eq7 : sin (β - γ) = sin β * cos γ - cos β * sin γ := by 
      rw [sin_sub]

    have eq8 : sin (α - β) = sin α * cos β - cos α * sin β := by 
      rw [sin_sub]

    have eq9 : sin (α - γ) = sin α * cos γ - cos α * sin γ := by 
      rw [sin_sub]
    
    rw [eq4, eq5, eq6, eq7, eq8, eq9]
    ring_nf 
    <;> simp [sin_sq, cos_sq]
    <;> nlinarith [Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, Real.sin_sq_add_cos_sq γ]
  rw [eq3]
  <;> field_simp [(show sin (α - β) ≠ 0 by assumption), (show sin (α - γ) ≠ 0 by assumption), (show sin (β - γ) ≠ 0 by assumption)]