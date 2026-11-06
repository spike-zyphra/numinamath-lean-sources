import Mathlib

theorem algebra_283044 (x y z : ℝ) :
    x + y = 2 ∧ x * y - z ^ 2 = 1 ↔ (x = 1 ∧ y = 1 ∧ z = 0) := by
  constructor
  · -- Assume (x + y = 2 ∧ x * y - z ^ 2 = 1), we need to prove (x = 1 ∧ y = 1 ∧ z = 0)
    rintro ⟨h1, h2⟩
    have h3 : y = 2 - x := by linarith
    rw [h3] at h2
    have h4 : (x - 1)^2 + z^2 = 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg z]
    have hx : x = 1 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg z]
    have hz : z = 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg z]
    have hy : y = 1 := by
      linarith [h1, hx]
    exact ⟨hx, hy, hz⟩
  · -- Assume (x = 1 ∧ y = 1 ∧ z = 0), we need to prove (x + y = 2 ∧ x * y - z ^ 2 = 1)
    rintro ⟨hx, hy, hz⟩
    constructor
    · -- x + y = 2
      rw [hx, hy]
      norm_num
    · -- x * y - z ^ 2 = 1
      rw [hx, hy, hz]
      norm_num