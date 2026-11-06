import Mathlib

theorem algebra_154501 :
    {(x, y) : ℝ × ℝ | (x - 2 * y) ^ 2 + (y - 1) ^ 2 = 0} = {(2, 1)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume $(x-2y)^2 + (y-1)^2 = 0$.
    intro hx
    have h1 : (x - 2 * y) ^ 2 = 0 := by
      linarith [sq_nonneg (x - 2 * y), sq_nonneg (y - 1)]
    have h2 : (y - 1) ^ 2 = 0 := by
      linarith [sq_nonneg (x - 2 * y), sq_nonneg (y - 1)]
    have h3 : x - 2 * y = 0 := by
      rwa [sq_eq_zero_iff] at h1
    have h4 : y - 1 = 0 := by
      rwa [sq_eq_zero_iff] at h2
    constructor
    · linarith
    · linarith
  · -- Assume $(x = 2 ∧ y = 1)$, we need to prove $(x-2y)^2 + (y-1)^2 = 0$.
    rintro ⟨hx, hy⟩
    rw [hx, hy]
    norm_num