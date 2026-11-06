import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_62334 :
    {x : ℝ | 0 < (x^3 - 8) / x ∧ x - 2 < sqrt ((x^3 - 8) / x)} = {x | x < 0 ∨ 2 < x} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- First equivalence implication.
    rintro ⟨hx1, hx2⟩
    by_cases h1 : x < 0
    · -- First case, x < 0
      left
      exact h1
    · -- Assume not x < 0, so x ≥ 0.
      have h1 : x ≥ 0 := by nlinarith
      by_cases h2 : x = 0
      · -- x = 0 case, which can't happen.
        rw [h2] at hx1
        norm_num at hx1
      · -- Assume not x < 0 and x ≠ 0.
        have h3 : 0 < x := by
          by_cases h3 : x > 0
          · linarith
          · -- Assume x > 0 doesn't hold, so x = 0
            have h4 : x ≤ 0 := by linarith
            have h4' : x = 0 := by linarith
            contradiction
        by_cases h4 : x > 2
        · -- Second case direction.
          right
          linarith
        · -- Assume x ≤ 2.
          have h5 : x ≤ 2 := by nlinarith
          have hx3 : (x^3 - 8) / x ≤ 0 := by
            apply div_nonpos_of_nonpos_of_nonneg
            · -- Show that x ^ 3 - 8 ≤ 0
              nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x - 1)]
            · -- Show that x ≥ 0
              linarith
          nlinarith
  · -- Second implication direction.
    intro h
    rcases h with (h1 | h2)
    · -- Assume x < 0.
      have h10 : x < 0 := h1
      constructor
      · -- Show that (x^3 - 8) / x > 0
        apply div_pos_of_neg_of_neg
        · -- Show that x^3 - 8 < 0
          nlinarith [sq_pos_of_neg (show x < 0 by linarith), sq_nonneg (x ^ 2)]
        · -- Show that x < 0
          linarith
      · -- Show that x - 2 < sqrt ((x^3 - 8) / x)
        have h10 : x < 0 := h1
        have h3 : x^3 - 8 < 0 := by nlinarith [sq_pos_of_neg (show x < 0 by linarith), sq_nonneg (x ^ 2)]
        have h3' : (x^3 - 8) / x > 0 := by apply div_pos_of_neg_of_neg; linarith; linarith
        have h5 : x - 2 < 0 := by nlinarith
        have h4 : sqrt ((x^3 - 8) / x) ≥ 0 := Real.sqrt_nonneg ( (x^3 - 8) / x)
        nlinarith
    · -- Assume 2 < x.
      have h20 : 2 < x := h2
      constructor
      · -- Show that (x^3 - 8) / x > 0
        apply div_pos
        · -- Show that x^3 - 8 > 0
          nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x - 1)]
        · -- Show that x > 0
          nlinarith
      · -- Show that x - 2 < sqrt ((x^3 - 8) / x)
        have h20 : 2 < x := h2
        have h3 : (x^3 - 8) / x > 0 := by
          apply div_pos
          · -- Show that x^3 - 8 > 0
            nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x - 1)]
          · -- Show that x > 0
            nlinarith
        have h4 : sqrt ((x^3 - 8) / x) ≥ 0 := Real.sqrt_nonneg ( (x^3 - 8) / x)
        have h5 : x - 2 ≥ 0 := by linarith
        have h6 : (sqrt ((x^3 - 8) / x)) ^ 2 = (x^3 - 8) / x := by
          rw [Real.sq_sqrt]
          linarith
        have h7 : (x - 2) ^ 2 < (x^3 - 8) / x := by
          apply (lt_div_iff₀ (by linarith)).mpr
          nlinarith [sq_nonneg (x - 2), sq_nonneg (x + 1), sq_nonneg (x ^ 2), sq_nonneg (x - 1)]
        nlinarith [Real.sqrt_nonneg ((x^3 - 8) / x), h4, h6, sq_nonneg (sqrt ((x^3 - 8) / x) - (x - 2)), h5]