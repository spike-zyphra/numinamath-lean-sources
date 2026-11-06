import Mathlib

theorem algebra_9621 {α β : ℝ} (h : α ≠ β) (h1 : α^2 - 19 * α + 53 = 0) (h2 : β^2 - 19 * β + 53 = 0) :
    (α - β)^2 = 149 := by
  have h3 : α^2 - β^2 = 19 * (α - β) := by
    linarith [h1, h2]
  have h4 : (α - β) * (α + β) = 19 * (α - β) := by
    have h5 : α^2 - β^2 = (α - β) * (α + β) := by ring
    rw [h5] at h3
    linarith
  have h6 : α + β = 19 := by
    apply (mul_right_inj' (sub_ne_zero.mpr h)).mp
    linarith
  have h7 : α * β = 53 := by
    nlinarith [h1, h2, h6]
  have h8 : (α - β) ^ 2 = (α + β)^2 - 4 * (α * β) := by
    ring
  rw [h8, h6, h7]
  norm_num