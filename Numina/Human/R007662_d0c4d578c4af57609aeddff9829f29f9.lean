import Mathlib

/- 4. Given $\sin \alpha+\cos \alpha=-\frac{1}{5}(0<\alpha<\pi)$, then $\tan \alpha=$ $\qquad$ -/
theorem algebra_182801 (α : ℝ) (h₀ : α ∈ Set.Ioo 0 Real.pi) (h₁ : Real.sin α + Real.cos α = -1 / 5) :
    Real.tan α = -3 / 4 := by 
  have h₂ : 0 < α ∧ α < Real.pi := h₀
  have h₃ : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi h₂.1 h₂.2
  have h₄ : Real.sin α = 3 / 5 := by
    nlinarith [Real.sin_sq_add_cos_sq α]
  have h₅ : Real.cos α = -4 / 5 := by
    nlinarith [Real.sin_sq_add_cos_sq α]
  have h₆ : Real.tan α = -3 / 4 := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp [h₃.ne', h₅]
    aesop
  exact h₆