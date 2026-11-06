import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_611140:
  {(x, y) : ℝ × ℝ | x ^ 4 = x ^ 2 * y ^ 2} = {(x, y) | x= 0 ∨ x = y ∨ x = -y} := by 
    ext ⟨x, y⟩
    constructor

    --From left to right. We divide it into two cases depending on whether x=0 or not.
    intro h
    simp_all
    by_cases xe0 : x = 0
    left; exact xe0
    have xne0: x ≠ 0 := by push_neg at xe0; exact xe0
    have x2ne0 : x^2 ≠ 0 := by  exact (pow_ne_zero 2 xne0)

    have : 4 = 2 + 2 := by norm_num
    rw [this] at h; rw [pow_add] at h
    field_simp at h
    simp [xne0]
    exact sq_eq_sq_iff_eq_or_eq_neg.mp h

    --From right to left. A simple calculation.
    intro h
    simp_all
    rcases h with h|h|h
    simp [h]
    simp [h]; ring
    simp [h]; ring
  