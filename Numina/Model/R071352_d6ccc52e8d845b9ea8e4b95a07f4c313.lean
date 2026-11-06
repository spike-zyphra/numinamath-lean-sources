import Mathlib

theorem algebra_198175 (α : ℝ) (h : Real.tan α = -1 / 2) :
    (2 * Real.cos α - Real.sin α) / (Real.sin α + Real.cos α) = 5 := by
  have h1 : Real.cos α ≠ 0 := by
    by_contra h2
    have htan : Real.tan α = 0 := by
      rw [Real.tan_eq_sin_div_cos]
      simp [h2]
    linarith [h, htan]
  have h2 : Real.sin α = -1 / 2 * Real.cos α := by
    have htan : Real.tan α = Real.sin α / Real.cos α := by
      rw [Real.tan_eq_sin_div_cos]
    rw [htan] at h
    field_simp [h1] at h ⊢
    linarith
  have h3 : Real.sin α + Real.cos α ≠ 0 := by
    by_contra h4
    have h5 : Real.sin α = - Real.cos α := by linarith
    rw [h5] at h2
    have h6 : Real.cos α = 0 := by
      nlinarith
    contradiction
  have h4 : 2 * Real.cos α - Real.sin α = 5 / 2 * Real.cos α := by
    rw [h2]
    linarith
  have h5 : Real.sin α + Real.cos α = 1 / 2 * Real.cos α := by
    rw [h2]
    linarith
  rw [h4, h5]
  -- $\frac{5/2 \cdot \cos \alpha}{1/2 \cdot \cos \alpha} = \frac{5/2}{1/2} \cdot \frac{\cos \alpha}{\cos \alpha} = 5$ since Real.cos α ≠ 0 from h1
  have h8 : Real.cos α ≠ 0 := h1
  field_simp [show (1 / 2 * Real.cos α) ≠ 0 by
    intro h9
    have h10 : Real.cos α = 0 := by
      nlinarith
    contradiction]
  <;> nlinarith [show Real.cos α ≠ 0 from h1]