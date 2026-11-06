import Mathlib

theorem algebra_232613 (x y z : ℝ) :
    x + y = 2 ∧ x * y - z ^ 2 = 1 ↔ x = 1 ∧ y = 1 ∧ z = 0 := by
  constructor
  · -- Assume x + y = 2 ∧ x * y - z ^ 2 = 1, prove x = 1 ∧ y = 1 ∧ z = 0
    rintro ⟨h1, h2⟩
    have h3 : y = 2 - x := by linarith
    rw [h3] at h2
    have h4 : (x - 1) ^ 2 + z ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg z]
    have hx1 : (x - 1) ^ 2 = 0 := by
      linarith [sq_nonneg (x - 1), sq_nonneg z]
    have hz1 : z ^ 2 = 0 := by
      linarith [sq_nonneg (x - 1), sq_nonneg z]
    have hx : x = 1 := by
      nlinarith [pow_eq_zero hx1]
    have hy : y = 1 := by
      linarith [hx, h1]
    have hz : z = 0 := by
      nlinarith [pow_eq_zero hz1]
    exact ⟨hx, hy, hz⟩
  · -- Assume x = 1 ∧ y = 1 ∧ z = 0, prove x + y = 2 ∧ x * y - z ^ 2 = 1
    rintro ⟨hx, hy, hz⟩
    constructor
    · -- Show x + y = 2
      linarith [hx, hy]
    · -- Show x * y - z ^ 2 = 1
      rw [hx, hy, hz]
      norm_num