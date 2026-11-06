import Mathlib

open Real

theorem algebra_12864 :
  {x: ℝ | x ≠ -1 ∧ x ≠ -7 ∧ (1 / (x + 1) + 3 / (x + 7) ≥ 2 / 3)} = Set.Ioc (-7) (-4) ∪ Set.Ioc (-1) 2 := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Ioc]
  constructor
  · -- Assume x is in the left side, prove x is in the right side
    rintro ⟨h1, h2, h3⟩
    have h4 : x + 1 ≠ 0 := by
      intro h
      apply h1
      linarith
    have h5 : x + 7 ≠ 0 := by
      intro h
      apply h2
      linarith
    have h6 : 1 / (x + 1) + 3 / (x + 7) - 2 / 3 ≥ 0 := by linarith
    have h7 : (1 / (x + 1) + 3 / (x + 7) - 2 / 3) = ( -2 * (x + 4) * (x - 2) ) / (3 * (x + 1) * (x + 7)) := by
      field_simp [(show x + 1 ≠ 0 by assumption), (show x + 7 ≠ 0 by assumption)]
      ring
    rw [h7] at h6
    have h8 : ( -2 * (x + 4) * (x - 2) ) / (3 * (x + 1) * (x + 7)) ≥ 0 := h6
    have h9 : (( -2 * (x + 4) * (x - 2) ) ) * (3 * (x + 1) * (x + 7)) ≥ 0 := by
      have h9 : (3 * (x + 1) * (x + 7)) ≠ 0 := by
        have h10 : x + 1 ≠ 0 := by
          intro h
          apply h1
          linarith
        have h11 : x + 7 ≠ 0 := by
          intro h
          apply h2
          linarith
        simp [h10, h11]
      have h100 : (( -2 * (x + 4) * (x - 2) ) / (3 * (x + 1) * (x + 7)) ) ≥ 0 := h6
      apply (div_nonneg_iff).mp at h100
      cases h100 with
      | inl h1 =>
        nlinarith
      | inr h2 =>
        nlinarith
    have h10 : (-7 < x ∧ x ≤ -4) ∨ (-1 < x ∧ x ≤ 2) := by
      by_cases h99 : 3 * (x + 1) * (x + 7) > 0
      · -- If 3 * (x+1) * (x+7) > 0, then the numerator must be >= 0
        have h17 : -2 * (x + 4) * (x - 2) ≥ 0 := by
          have h17 : (( -2 * (x + 4) * (x - 2) ) ) * (3 * (x + 1) * (x + 7)) ≥ 0 := h9
          nlinarith
        have h68 : (x + 4) * (x - 2) ≤ 0 := by nlinarith
        have h43 : x > -1 ∨ x < -7 := by
          by_contra h
          push_neg at h
          have h4 : 3 * (x + 1) * (x + 7) ≤ 0 := by
            nlinarith [sq_nonneg (x + 1), sq_nonneg (x + 7)]
          nlinarith
        cases h43 with
        | inl h10 =>
          -- If x > -1.
          have h46 : x > -1 := h10
          have h27 : x ≤ 2 := by nlinarith
          right
          constructor
          · -- -1 < x
            linarith
          · -- x ≤ 2
            linarith
        | inr h11 =>
          -- If x < -7, contradicts with h43 : x < -7
          have h18 : x < -7 := h11
          nlinarith [sq_pos_of_ne_zero (show (x + 1) ≠ 0 by
            intro h
            apply h1
            linarith
          ), sq_pos_of_ne_zero (show (x + 7) ≠ 0 by
            intro h
            apply h2
            linarith
          ), sq_nonneg (x + 4), sq_nonneg (x + 1), sq_nonneg (x + 7)]
      by_cases h99 : 3 * (x + 1) * (x + 7) < 0
      · -- If 3 * (x+1) * (x+7) < 0, then the numerator must be <= 0
        have h102 : -2 * (x + 4) * (x - 2) ≤ 0 := by
          have h97 : (( -2 * (x + 4) * (x - 2) ) ) * (3 * (x + 1) * (x + 7)) ≥ 0 := h9
          nlinarith
        have h110 : (x + 4) * (x - 2) ≥ 0 := by nlinarith
        have h19 : -7 < x := by
          nlinarith [sq_pos_of_ne_zero (show (x + 1) ≠ 0 by
            intro h
            apply h1
            linarith
          ), sq_pos_of_ne_zero (show (x + 7) ≠ 0 by
            intro h
            apply h2
            linarith
          ), sq_nonneg (x + 4), sq_nonneg (x + 1), sq_nonneg (x + 7)]
        have h18 : x ≤ -4 := by
          nlinarith
        left
        constructor
        · -- -7 < x
          linarith
        · -- x ≤ -4
          linarith
      -- If 3 * (x+1) * (x+7) = 0
      have h014 : 3 * (x + 1) * (x + 7) = 0 := by nlinarith
      exfalso
      have h18 : x + 1 = 0 ∨ x + 7 = 0 := by
        have h4 : 3 * (x + 1) * (x + 7) = 0 := h014
        have h5 : (x + 1) * (x + 7) = 0 := by
          linarith
        cases mul_eq_zero.mp h5 with
        | inl h7 => 
          left; linarith
        | inr h10 => 
          right; linarith
      cases h18 with
      | inl h19 =>
        apply h1
        linarith
      | inr h20 =>
        apply h2
        linarith
    tauto
  · -- Assume x is in the right side, prove x is in the left side
    rintro (h | h)
    · -- Case where x ∈ (-7, -4]
      have h1 : -7 < x := h.1
      have h2 : x ≤ -4 := h.2
      have h3 : x + 1 ≠ 0 := by
        nlinarith
      have h4 : x + 7 ≠ 0 := by
        nlinarith
      constructor
      · -- x ≠ -1
        intro h
        nlinarith
      constructor
      · -- x ≠ -7
        intro h
        nlinarith
      · -- Show 1/(x+1) + 3/(x+7) ≥ 2/3
        have h5 : 1 / (x + 1) + 3 / (x + 7) - 2 / 3 ≥ 0 := by
          have h7 : 1 / (x + 1) + 3 / (x + 7) - 2 / 3 = ( -2 * (x + 4) * (x - 2) ) / (3 * (x + 1) * (x + 7)) := by
            field_simp [show x + 1 ≠ 0 by nlinarith, show x + 7 ≠ 0 by nlinarith]
            ring
          rw [h7]
          have h8 : ( -2 * (x + 4) * (x - 2) ) / (3 * (x + 1) * (x + 7)) ≥ 0 := by
            apply div_nonneg_of_nonpos
            · -- Show -2(x+4)(x-2) ≤ 0
              nlinarith [sq_nonneg (x + 4), sq_nonneg (x - 2)]
            · -- Show 3(x+1)(x+7) ≤ 0
              nlinarith [sq_nonneg (x + 1), sq_nonneg (x + 7)]
          linarith
        linarith
    · -- Case where x ∈ (-1, 2]
      have h1 : -1 < x := h.1
      have h2 : x ≤ 2 := h.2
      have h3 : x + 1 ≠ 0 := by
        nlinarith
      have h4 : x + 7 ≠ 0 := by
        nlinarith
      constructor
      · -- x ≠ -1
        intro h
        nlinarith
      constructor
      · -- x ≠ -7
        intro h
        nlinarith
      · -- Show 1/(x+1) + 3/(x+7) ≥ 2/3
        have h5 : 1 / (x + 1) + 3 / (x + 7) - 2 / 3 ≥ 0 := by
          have h7 : 1 / (x + 1) + 3 / (x + 7) - 2 / 3 = ( -2 * (x + 4) * (x - 2) ) / (3 * (x + 1) * (x + 7)) := by
            field_simp [show x + 1 ≠ 0 by nlinarith, show x + 7 ≠ 0 by nlinarith]
            ring
          rw [h7]
          have h8 : ( -2 * (x + 4) * (x - 2) ) / (3 * (x + 1) * (x + 7)) ≥ 0 := by
            apply div_nonneg
            · -- Show numerator ≥ 0
              nlinarith [sq_nonneg (x + 4), sq_nonneg (x - 2)]
            · -- Show denominator ≥ 0
              nlinarith [sq_nonneg (x + 1), sq_nonneg (x + 7)]
          linarith
        linarith