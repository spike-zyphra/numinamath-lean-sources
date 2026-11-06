import Mathlib

theorem algebra_5047 {x : ℝ} (hx : x ≠ -2 ∧ x ≠ -4 ∧ x ≠ 6 ∧ x ≠ 4) : 1 / (x + 2) - 1 / (x + 4) = 1 / (x - 6) - 1 / (x - 4) ↔ x = 1 := by 
  constructor
  · intro h
    have h1 : x + 2 ≠ 0 := by intro h1; apply hx.left; linarith
    have h2 : x + 4 ≠ 0 := by intro h1; apply hx.right.left; linarith
    have h3 : x - 6 ≠ 0 := by intro h1; apply hx.right.right.left; linarith
    have h4 : x - 4 ≠ 0 := by intro h1; apply hx.right.right.right; linarith
    field_simp [h1, h2, h3, h4] at h
    nlinarith [sq_nonneg (x - 1)]
  · intro h
    rw [h]
    norm_num