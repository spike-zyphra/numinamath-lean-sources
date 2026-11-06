import Mathlib

theorem algebra_148669 :
    {x : ℝ | x - 2 ≠ 0 ∧ x - 1 ≠ 0 ∧ x + 1 ≠ 0 ∧ x + 2 ≠ 0 ∧ (x + 2) / (x - 2) - (x + 1) / (x - 1) - (x - 1) / (x + 1) + (x - 2) / (x + 2) = 2 * (1 / (x - 2) - 1 / (x - 1) - 1 / (x + 1) + 1 / (x + 2))} = {0} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x is in the left side, prove it's in the right side
    rintro ⟨hx2, hx1, hxn1, hxn2, heq⟩
    have hx3 : x - 2 ≠ 0 := hx2
    have hx4 : x - 1 ≠ 0 := hx1
    have hx5 : x + 1 ≠ 0 := hxn1
    have hx6 : x + 2 ≠ 0 := hxn2
    field_simp [(show x - 2 ≠ 0 by assumption), (show x - 1 ≠ 0 by assumption), (show x + 1 ≠ 0 by assumption), (show x + 2 ≠ 0 by assumption)] at heq
    have h0 : x = 0 := by
      nlinarith [sq_pos_of_ne_zero (show (x - 2 : ℝ) ≠ 0 by assumption), sq_pos_of_ne_zero (show (x - 1 : ℝ) ≠ 0 by assumption), sq_pos_of_ne_zero (show (x + 1 : ℝ) ≠ 0 by assumption), sq_pos_of_ne_zero (show (x + 2 : ℝ) ≠ 0 by assumption), sq_nonneg (x), sq_nonneg (x^2 - 1)]
    linarith
  · -- Assume x is in the right side, prove it's in the left side
    intro h0
    rw [h0]
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num