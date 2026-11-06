import Mathlib

open Real

/- 11. If

$$

\begin{array}{l}
\tan \theta=\frac{\sin \alpha \cos \gamma-\sin \beta \sin \gamma}{\cos \alpha \cos \gamma-\cos \beta \sin \gamma} \\
\tan \varphi=\frac{\sin \alpha \sin \gamma-\sin \beta \cos \gamma}{\cos \alpha \sin \gamma-\cos \beta \cos \gamma}
\end{array}

$$


Prove: $\tan (\theta+\varphi)=\tan (\alpha+\beta)$. -/
theorem algebra_107288 (θ α β γ φ : ℝ)
  (hθ : ∀ (k : ℤ), θ ≠ (2 * k + 1) * π / 2) (hφ : ∀ (k : ℤ), φ ≠ (2 * k + 1) * π / 2)
  (hd₁ : cos α * cos γ - cos β * sin γ ≠ 0) (hd₂ : cos α * sin γ - cos β * cos γ ≠ 0)
  (h₀ : tan θ = (sin α * cos γ - sin β * sin γ) / (cos α * cos γ - cos β * sin γ))
  (h₁ : tan φ = (sin α * sin γ - sin β * cos γ) / (cos α * sin γ - cos β * cos γ)) :
  tan (θ + φ) = tan (α + β) := by
  -- first express tan θ + tan φ with one denominator
  have ht₁ : tan θ + tan φ = ((sin α * cos γ - sin β * sin γ) * (cos α * sin γ - cos β * cos γ) +  (sin α * sin γ - sin β * cos γ) * (cos α * cos γ - cos β * sin γ)) / ((cos α * cos γ - cos β * sin γ) * (cos α * sin γ - cos β * cos γ)) := by
    rw [h₀, h₁]
    field_simp
  -- express the numerator as sin (α + β) * k
  have ht₁' : (sin α * cos γ - sin β * sin γ) * (cos α * sin γ - cos β * cos γ) +  (sin α * sin γ - sin β * cos γ) * (cos α * cos γ - cos β * sin γ) = sin (α + β) *  (cos (α - β) * sin (2 * γ) - 1) := by calc
     (sin α * cos γ - sin β * sin γ) * (cos α * sin γ - cos β * cos γ) +  (sin α * sin γ - sin β * cos γ) * (cos α * cos γ - cos β * sin γ) = sin α * cos γ * sin γ * cos α * 2  - sin α *  cos β * (sin γ ^ 2 + cos γ ^ 2) + cos γ * sin β * sin γ * cos β * 2 - sin β * cos α * (sin γ^2 + cos γ^2) := by ring
    _ = sin α * cos γ * sin γ * cos α * 2 * (sin β^2 + cos β^2) - sin α * cos β - sin β * cos α + cos γ * sin β * sin γ * cos β * 2 * (sin α^2 + cos α^2) := by
      repeat rw [sin_sq_add_cos_sq]
      ring
    _ = _ := by rw [sin_add, cos_sub, sin_two_mul]; ring
  rw [ht₁'] at ht₁
  clear ht₁'
  -- then express 1 - tan θ tan φ with one denominator
  have ht₂ : 1 - tan θ * tan φ = ((cos α * cos γ - cos β * sin γ) * (cos α * sin γ - cos β * cos γ) - (sin α * cos γ - sin β * sin γ) * (sin α * sin γ - sin β * cos γ)) / ((cos α * cos γ - cos β * sin γ) * (cos α * sin γ - cos β * cos γ)) := by
    rw [h₀, h₁]
    field_simp
  -- an auxilarity fact that will be used to simplify numerator
  have aux : cos α^2 + cos β^2 - sin α^2 - sin β^2 = 2 * (cos α^2 * cos β^2 - sin α^2 * sin β^2) := by calc
    cos α^2 + cos β^2 - sin α^2 - sin β^2 = cos (2 * α) + cos (2 * β) := by rw [Real.cos_two_mul', Real.cos_two_mul']; ring
    _ = 2 * cos (α + β) * cos (α - β) := by rw [Real.two_mul_cos_mul_cos]; ring_nf
    _ = _ := by rw [cos_add, cos_sub]; ring
  -- express numerator as cos (α + β) * k
  have ht₂' : (cos α * cos γ - cos β * sin γ) * (cos α * sin γ - cos β * cos γ) - (sin α * cos γ - sin β * sin γ) * (sin α * sin γ - sin β * cos γ) = cos (α + β) *  (cos (α - β) * sin (2 * γ) - 1) := by calc
    (cos α * cos γ - cos β * sin γ) * (cos α * sin γ - cos β * cos γ) - (sin α * cos γ - sin β * sin γ) * (sin α * sin γ - sin β * cos γ) = -cos α * cos β * (sin γ^2 + cos γ^2) + sin γ * cos γ * (cos α^2 + cos β^2 - sin α^2 - sin β^2) + sin α * sin β * (sin γ^2 + cos γ^2) := by ring_nf
    _ = - cos α * cos β + cos α ^ 2 * cos γ * cos β ^ 2 * sin γ * 2 - cos γ * sin γ * sin α ^ 2 * sin β ^ 2 * 2 + sin α * sin β := by rw [sin_sq_add_cos_sq, aux]; ring
    _ = _ := by rw [cos_sub, cos_add, sin_two_mul]; ring
  rw [ht₂'] at ht₂
  clear ht₂' aux
  -- show that cos (α - β) * sin (2γ) - 1 cannot be 0, because it being 0 means sum of 4 squares are 0, two of which are nonzero by hypothesis
  have : cos (α - β) * sin (2 * γ) - 1 ≠ 0 := by
    by_contra h
    rw [cos_sub, sin_two_mul] at h
    have h₁ : ((sin α^2 + cos α^2) + (sin β^2 + cos β^2)) * (sin γ^2 + cos γ^2) = 2 := by
      repeat rw [sin_sq_add_cos_sq]
      norm_num
    have : (cos α * cos γ - cos β * sin γ)^2 + ((cos α * sin γ - cos β * cos γ)^2 + (sin α * cos γ - sin β * sin γ)^2 + (sin α * sin γ - sin β * cos γ)^2) = 0 := by
      linear_combination h₁ - 2 * h
    have : (cos α * cos γ - cos β * sin γ)^2 = 0 := by exact add_eq_zero_iff_of_nonneg (by positivity) (by positivity) |>.mp this |>.left
    simp at this
    contradiction
  -- finally use tan addition and division formula to show target is true
  rw [Real.tan_add' ⟨hθ, hφ⟩, tan_eq_sin_div_cos (α + β), ht₁, ht₂]
  by_cases h : cos (α + β) = 0
  . rw [h]; simp
  . field_simp; ring