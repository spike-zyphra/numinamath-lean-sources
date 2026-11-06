import Mathlib

theorem algebra_21514 : Set.ncard {(x, y) : ℝ × ℝ | (x + y) ^ 2 = (x + 1) * (y - 1)} = 1 := by
  have h1 : {(x, y) : ℝ × ℝ | (x + y) ^ 2 = (x + 1) * (y - 1)} = {(-1, 1)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Assume (x + y)^2 = (x + 1)(y - 1), prove (x, y) = (-1, 1)
      rintro H
      have h2 : (x + y) ^ 2 = (x + 1) * (y - 1) := H
      have h4 : (x + 1) ^ 2 + (y - 1) ^ 2 = 0 := by
        nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x + 1), sq_nonneg (y - 1)]
      have h5 : x + 1 = 0 := by nlinarith [sq_nonneg (x + 1), sq_nonneg (y - 1)]
      have h6 : y - 1 = 0 := by nlinarith [sq_nonneg (x + 1), sq_nonneg (y - 1)]
      have hx : x = -1 := by linarith
      have hy : y = 1 := by linarith
      exact ⟨hx, hy⟩
    · -- Assume (x, y) = (-1, 1), prove (x + y)^2 = (x + 1) * (y - 1)
      rintro ⟨rfl, rfl⟩
      norm_num
  rw [h1]
  simp [Set.ncard_singleton]