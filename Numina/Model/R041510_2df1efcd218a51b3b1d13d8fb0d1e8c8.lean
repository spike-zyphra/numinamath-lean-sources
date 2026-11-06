import Mathlib

theorem algebra_166168 {x y : ℝ} (hx : x ≠ -y + 1) (hy : y ≠ 2 * x - 3) :
    4 / (x + y - 1) - 5 / (2 * x - y + 3) + 5 / 2 = 0 ∧
    3 / (x + y - 1) + 1 / (2 * x - y + 3) + 7 / 5 = 0 ↔ (x, y) = (2, -3) := by
  constructor
  · -- Assume the equations hold, prove (x, y) = (2, -3)
    rintro ⟨h1, h2⟩
    have h3 : x + y - 1 ≠ 0 := by
      intro h4
      apply hx
      linarith
    have h4 : 2 * x - y + 3 ≠ 0 := by
      by_contra h5
      have eq1 := h1
      have eq2 := h2
      field_simp [show x + y - 1 ≠ 0 by exact h3, show 2 * x - y + 3 = 0 by linarith [h5]] at eq1 eq2
      <;> nlinarith [sq_pos_of_ne_zero (show (x + y - 1 : ℝ) ≠ 0 by exact h3), sq_nonneg (x - 2), sq_nonneg (y + 3)]
    have eq1 : 4 * (2 * x - y + 3) - 5 * (x + y - 1) + (5 / 2) * (x + y - 1) * (2 * x - y + 3) = 0 := by
      have h5 : x + y - 1 ≠ 0 := h3
      have h6 : 2 * x - y + 3 ≠ 0 := h4
      field_simp [h5, h6] at h1 ⊢
      linarith
    have eq2 : 3 * (2 * x - y + 3) + (x + y - 1) + (7 / 5) * (x + y - 1) * (2 * x - y + 3) = 0 := by
      have h5 : x + y - 1 ≠ 0 := h3
      have h6 : 2 * x - y + 3 ≠ 0 := h4
      field_simp [h5, h6] at h2 ⊢
      linarith
    have hx3 : x = 2 := by
      nlinarith [sq_pos_of_ne_zero (show (x + y - 1 : ℝ) ≠ 0 by exact h3), sq_pos_of_ne_zero (show (2 * x - y + 3 : ℝ) ≠ 0 by exact h4), sq_nonneg (x - 2), sq_nonneg (y + 3)]
    have hy4 : y = -3 := by
      nlinarith [sq_pos_of_ne_zero (show (x + y - 1 : ℝ) ≠ 0 by exact h3), sq_pos_of_ne_zero (show (2 * x - y + 3 : ℝ) ≠ 0 by exact h4), sq_nonneg (x - 2), sq_nonneg (y + 3)]
    simp [Prod.ext_iff, hx3, hy4]
  · -- Assume (x, y) = (2, -3), prove equations
    rintro (h)
    simp [Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    constructor
    · -- Check first equation
      norm_num
    · -- Check second equation
      norm_num