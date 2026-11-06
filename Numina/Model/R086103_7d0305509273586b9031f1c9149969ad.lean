import Mathlib

theorem algebra_192577 {α β : ℝ} (h : α^2 - 10 * α + 20 = 0 ∧ β^2 - 10 * β + 20 = 0)
    (hroots : α ≠ β) : 1 / α + 1 / β = 1 / 2 := by
  have h₁ : α^2 - 10 * α + 20 = 0 := h.1
  have h₂ : β^2 - 10 * β + 20 = 0 := h.2

  have h3 : α ≠ 0 := by
    by_contra hα
    rw [hα] at h₁
    nlinarith

  have h4 : β ≠ 0 := by
    by_contra hβ
    rw [hβ] at h₂
    nlinarith

  have h5 : α + β = 10 := by
    have eq1 : α^2 - β^2 = 10 * (α - β) := by
      nlinarith
    have eq2 : α^2 - β^2 = (α - β) * (α + β) := by ring
    rw [eq2] at eq1 -- (α - β) * (α + β) = 10 * (α - β)
    have h6 : α - β ≠ 0 := by
      intro h
      apply hroots
      linarith
    have h7 : (α + β) = 10 := by
      apply (mul_left_inj' h6).mp
      linarith
    exact h7

  have h6 : α * β = 20 := by
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero_of_ne hroots), sq_pos_of_ne_zero (h3), sq_pos_of_ne_zero (h4)]

  -- Simplify the target
  -- $A=\frac{1}{\alpha} + \frac{1}{\beta} = \frac{\beta + \alpha}{\alpha \cdot \beta} = \frac{\alpha + \beta}{\alpha \cdot \beta} = \frac{10}{20} = \frac{1}{2}$
  have h7 : 1 / α + 1 / β = (α + β) / (α * β) := by
    field_simp [h3, h4]
    <;> ring

  rw [h7]
  rw [h5, h6]
  norm_num
  <;> try { linarith }
  <;> try { norm_num }
  <;> try { linarith }