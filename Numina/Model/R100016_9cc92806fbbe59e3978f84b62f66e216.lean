import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_292750 :
  IsLeast {t : ℝ | ∃ x y : ℝ, x > 0 ∧ y > 0 ∧ x + y = 6 ∧ t = 1 / x + 1 / y} (2 / 3) := by
  constructor
  · -- Show that 2/3 is achievable with x=y=3
    use 3, 3
    constructor
    · norm_num -- x > 0
    constructor
    · norm_num -- y > 0
    constructor
    · norm_num -- x + y = 6
    · norm_num -- 2/3 = 1/3 + 1/3
  · -- Show that 2/3 is a lower bound
    intro t ht
    rcases ht with ⟨x, y, hx, hy, hxy, ht⟩
    have h : 1 / x + 1 / y ≥ 2 / 3 := by
      have h1 : x + y = 6 := hxy
      have h2 : x > 0 := hx
      have h3 : y > 0 := hy
      have h4 : x * y ≤ 9 := by
        nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 3), h1]
      have h5 : 18 - 2 * (x * y) ≥ 0 := by linarith
      have h6 : 1 / x + 1 / y - 2 / 3 ≥ 0 := by
        have h7 : 1 / x + 1 / y - 2 / 3 = (18 - 2 * (x * y)) / (3 * x * y) := by
          field_simp [show x ≠ 0 by linarith, show y ≠ 0 by linarith]
          nlinarith [h1]
        rw [h7]
        apply div_nonneg
        linarith
        all_goals
          positivity
      linarith
    linarith [ht, h]