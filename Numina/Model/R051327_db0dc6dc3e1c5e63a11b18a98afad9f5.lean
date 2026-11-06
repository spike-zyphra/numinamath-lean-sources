import Mathlib

theorem algebra_327375 {α : ℝ} (h : α^2 + α - 1 / 4 = 0) :
    (α^3 - 1) / (α^5 + α^4 - α^3 - α^2) = 20 := by
  have h1 : α^2 = -α + 1/4 := by linarith
  have h2 : α^3 = 5/4 * α - 1/4 := by
    calc
      α^3 = α * α^2 := by ring
      _ = α * (-α + 1/4) := by rw [h1]
      _ = -α^2 + (1/4) * α := by ring
      _ = -(-α + 1/4) + (1/4) * α := by rw [h1]
      _ = 5/4 * α - 1/4 := by ring
  have h3 : α^4 = -3/2 * α + 5/16 := by
    calc
      α^4 = (α^2)^2 := by ring
      _ = (-α + 1/4)^2 := by rw [h1]
      _ = α^2 - (1/2) * α + 1/16 := by ring_nf
      _ = (-α + 1/4) - (1/2) * α + 1/16 := by rw [h1]
      _ = -3/2 * α + 5/16 := by ring_nf
  have h4 : α^5 = 29/16 * α - 3/8 := by
    calc 
      α^5 = α * α^4 := by ring
      _ = α * (-3/2 * α + 5/16) := by rw [h3]
      _ = -3/2 * α^2 + 5/16 * α := by ring
      _ = -3/2 * (-α + 1/4) + 5/16 * α := by rw [h1]
      _ = 29/16 * α - 3/8 := by ring_nf
  have num : α^3 - 1 = 5/4 * (α - 1) := by
    rw [h2]
    ring_nf
  have denom : α^5 + α^4 - α^3 - α^2 = 1/16 * (α - 1) := by
    rw [h4, h3, h2, h1]
    ring_nf
  have ha1 : α - 1 ≠ 0 := by
    by_contra h1'
    have h1_eq : α = 1 := by linarith
    rw [h1_eq] at h
    norm_num at h
  rw [num, denom]
  field_simp [ha1]
  <;> ring_nf <;> linarith