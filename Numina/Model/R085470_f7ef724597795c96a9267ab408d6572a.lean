import Mathlib

theorem algebra_163340 (x y : ℝ) :
    x^2 + (1 - y)^2 + (x - y)^2 = 1 / 3 ↔ x = 1 / 3 ∧ y = 2 / 3 := by
  constructor
  · -- Assume equation holds, prove x = 1/3 ∧ y = 2/3
    intro h
    have h1 : (x - 1 / 3)^2 + (y - 2 / 3)^2 = 0 := by 
      nlinarith [sq_nonneg (x - 1 / 3), sq_nonneg (y - 2 / 3), sq_nonneg (x - y), sq_nonneg (x + y - 1)]
    have hx : (x - 1 / 3)^2 = 0 := by
      linarith [sq_nonneg (x - 1 / 3), sq_nonneg (y - 2 / 3)]
    have hy : (y - 2 / 3)^2 = 0 := by
      linarith [sq_nonneg (x - 1 / 3), sq_nonneg (y - 2 / 3)]
    have hx2 : x - 1 / 3 = 0 := by
      rwa [sq_eq_zero_iff] at hx
    have hy2 : y - 2 / 3 = 0 := by
      rwa [sq_eq_zero_iff] at hy
    constructor
    · linarith [hx2]
    · linarith [hy2]
  · -- Assume x = 1/3 ∧ y = 2/3, prove equation
    rintro ⟨hx, hy⟩
    rw [hx, hy]
    norm_num