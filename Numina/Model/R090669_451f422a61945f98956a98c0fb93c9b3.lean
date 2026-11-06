import Mathlib

theorem algebra_321403 {α β : ℝ} (h : α ≠ β) (h1 : α^2 + α - 1 = 0) (h2 : β^2 + β - 1 = 0) :
    α^3 / β + β^3 / α = -7 := by
  have h3 : α - β ≠ 0 := by exact sub_ne_zero.mpr h
  have h4 : α + β = -1 := by
    have eq1 : α^2 + α - 1 = 0 := h1
    have eq2 : β^2 + β - 1 = 0 := h2
    have eq3 : α^2 + α - 1 - (β^2 + β - 1) = 0 := by linarith
    have eq4 : (α - β) * (α + β + 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp eq4) with h5 h6
    · 
      exfalso
      exact h (by linarith)
    · 
      linarith
  have h5 : α * β = -1 := by
    have eq1 : α^2 + α - 1 = 0 := h1
    have eq2 : β^2 + β - 1 = 0 := h2
    have eq3 : (α + β) ^ 2 - 2 * (α * β) + (α + β) - 2 = 0 := by
      nlinarith
    rw [show α + β = -1 by linarith [h4]] at eq3
    nlinarith
  have h6 : α ≠ 0 := by
    by_contra h7
    rw [h7] at h1
    nlinarith
  have h7 : β ≠ 0 := by
    by_contra h8
    rw [h8] at h2
    nlinarith
  have h8 : α ^ 2 = 1 - α := by linarith
  have h9 : β ^ 2 = 1 - β := by linarith
  have h10 : α ^ 4 = 2 - 3 * α := by
    calc
      α ^ 4 = (α ^ 2) ^ 2 := by ring
      _ = (1 - α) ^ 2 := by rw [h8]
      _ = 1 - 2 * α + α ^ 2 := by ring
      _ = 1 - 2 * α + (1 - α) := by rw [h8]
      _ = 2 - 3 * α := by ring
  have h11 : β ^ 4 = 2 - 3 * β := by
    calc
      β ^ 4 = (β ^ 2) ^ 2 := by ring
      _ = (1 - β) ^ 2 := by rw [h9]
      _ = 1 - 2 * β + β ^ 2 := by ring
      _ = 1 - 2 * β + (1 - β) := by rw [h9]
      _ = 2 - 3 * β := by ring
  have h12 : α ^ 4 + β ^ 4 = 7 := by
    have h14 : α ^ 4 + β ^ 4 = (2 - 3 * α) + (2 - 3 * β) := by
      rw [h10, h11]
    rw [h14]
    nlinarith [h4]
  have eq3 : α ^ 3 / β + β ^ 3 / α = (α ^ 4 + β ^ 4) / (α * β) := by
    field_simp [show β ≠ 0 by exact h7, show α ≠ 0 by exact h6]
    <;> ring
  rw [eq3, h12, h5]
  norm_num