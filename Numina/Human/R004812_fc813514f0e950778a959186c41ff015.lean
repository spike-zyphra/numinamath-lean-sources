import Mathlib

open Real

/- Given $\tan \alpha=2$, find the value of $3\sin ^{2}\alpha-\cos \alpha\sin \alpha+1$. -/
theorem algebra_448190 (α : ℝ) (h : tan α = 2) :
    3 * sin α ^ 2 - cos α * sin α + 1 = 3 := by
  rw [tan_eq_sin_div_cos] at h
  have h₁ : cos α ≠ 0 := by
    intro k
    simp [k] at h
  field_simp at h
  have h₂ : cos α ^ 2 + sin α ^ 2 = 1 := cos_sq_add_sin_sq α
  rw [h] at h₂ ⊢
  linarith only [h₂]
