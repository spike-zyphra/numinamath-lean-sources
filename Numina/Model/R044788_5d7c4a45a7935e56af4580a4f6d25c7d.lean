import Mathlib

open Real Set

theorem algebra_18608 :
    IsLeast {t | ∃(x y : ℝ), 0 < x ∧ 0 < y ∧ x + 1/y = 5 ∧ t = 1/x + y} (4/5) := by
  constructor
  · -- Show that 4/5 is in the set
    use 5 / 2, 2 / 5
    constructor
    · -- Show x is positive
      norm_num
    constructor
    · -- Show y is positive
      norm_num
    constructor
    · -- Show x + 1/y = 5
      norm_num
    · -- Show 4/5 = 1/x + y
      norm_num
  · -- Show that 4/5 is the minimum
    intro t ht
    rcases ht with ⟨x, y, hx, hy, h, ht⟩
    have h1 : x + 1 / y = 5 := h
    have h2 : t = 1 / x + y := ht
    have h3 : 1 / x + y ≥ 4 / 5 := by
      have h4 : x > 0 := hx
      have h5 : y > 0 := hy
      have h6 : x + 1 / y = 5 := h
      have h7 : x * y + 1 = 5 * y := by
        have h8 : y > 0 := hy
        field_simp at h6
        nlinarith
      have h8 : 5 - x > 0 := by
        nlinarith [h7, sq_nonneg (x * y), sq_nonneg (x - 5 / 2), sq_nonneg (y - 2 / 5), mul_pos hx hy]
      have h9 : y = 1 / (5 - x) := by
        field_simp [(show 5 - x ≠ 0 by linarith [h8])]
        nlinarith [h7, sq_nonneg (x * y), sq_nonneg (x - 5 / 2), sq_nonneg (y - 2 / 5), mul_pos hx hy]
      rw [h9]
      have hx1_pos : 0 < x := hx
      have hx2_pos : 0 < 5 - x := by nlinarith [h8]
      have h10 : 1 / x + 1 / (5 - x) ≥ 4 / 5 := by
        have h11 : 1 / x + 1 / (5 - x) - 4 / 5 ≥ 0 := by
          have h12 : 1 / x + 1 / (5 - x) - 4 / 5 = ( (2 * x - 5) ^ 2 ) / (5 * x * (5 - x)) := by
            field_simp
            <;> ring
          rw [h12]
          apply div_nonneg
          · -- Numerator is non-negative
            nlinarith [sq_nonneg (2 * x - 5)]
          · -- Denominator is non-negative
            positivity
        linarith
      linarith
    linarith [ht, h3]