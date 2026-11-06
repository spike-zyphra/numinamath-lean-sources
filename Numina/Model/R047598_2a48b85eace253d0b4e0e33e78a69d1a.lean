import Mathlib

theorem algebra_310634 {x : ℝ} (hx : x^2 - x - 1 = 0) (α : ℝ) (hα : α = x) :
    α^18 + 323 / α^6 = 5796 := by
  have h1 : α^2 = α + 1 := by
    rw [hα]
    have h_eq : x^2 = x + 1 := by linarith
    linarith
  have h2 : α ^ 3 = 2 * α + 1 := by 
    calc 
      α^3 = α * α^2 := by ring
      _ = α * (α + 1) := by rw [h1]
      _ = α^2 + α := by ring
      _ = (α + 1) + α := by rw [h1]
      _ = 2 * α + 1 := by ring
  have h3 : α ^ 4 = 3 * α + 2 := by 
    calc 
      α^4 = α * α^3 := by ring
      _ = α * (2 * α + 1) := by rw [h2]
      _ = 2 * α^2 + α := by ring
      _ = 2 * (α + 1) + α := by rw [h1]
      _ = (2 * α + 2) + α := by ring
      _ = 3 * α + 2 := by ring
  have h4 : α ^ 5 = 5 * α + 3 := by 
    calc 
      α^5 = α * α^4 := by ring
      _ = α * (3 * α + 2) := by rw [h3]
      _ = 3 * α^2 + 2 * α := by ring
      _ = 3 * (α + 1) + 2 * α := by rw [h1]
      _ = (3 * α + 3) + 2 * α := by ring
      _ = 5 * α + 3 := by ring
  have h5 : α ^ 6 = 8 * α + 5 := by 
    calc 
      α^6 = α * α^5 := by ring
      _ = α * (5 * α + 3) := by rw [h4]
      _ = 5 * α^2 + 3 * α := by ring
      _ = 5 * (α + 1) + 3 * α := by rw [h1]
      _ = (5 * α + 5) + 3 * α := by ring
      _ = 8 * α + 5 := by ring
  have h6 : α ^ 6 = 8 * α + 5 := h5
  have h7 : 1 / (α ^ 6) = 13 - 8 * α := by
    rw [h6]
    have h8 : 8 * α + 5 ≠ 0 := by
      by_contra h
      have h9 : 8 * α + 5 = 0 := by linarith
      have h10 : α ^ 2 = α + 1 := h1
      nlinarith [sq_nonneg (α - 1 / 2)]
    field_simp [h8]
    nlinarith [sq_nonneg (α - 1 / 2), h1]
  have h18 : α ^ 18 = 2584 * α + 1597 := by 
    have h8 : α ^ 6 = 8 * α + 5 := h5
    have h9 : α ^ 18 = (α ^ 6) ^ 3 := by ring
    rw [h9, h8]
    nlinarith [sq_nonneg (α - 1 / 2), h1, h2, h3, h4, h5]
  rw [show 323 / α^6 = 323 * (1 / α^6) by field_simp]
  rw [h7]
  nlinarith [h18, sq_nonneg (α - 1 / 2)]