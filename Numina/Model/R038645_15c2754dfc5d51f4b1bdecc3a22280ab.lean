import Mathlib

open Real Set

theorem algebra_20819 :
    IsLeast {z : ℝ | ∃ x y : ℝ, x > 0 ∧ y > 0 ∧ z = (x + 1 / y) * (x + 1 / y + 2018) +
      (y + 1 / x) * (y + 1 / x + 2018)} 8080 := by
  constructor
  · -- Show that 8080 is in the set
    use 1, 1
    norm_num
  · -- Show that for all z in the set, 8080 ≤ z
    intro z h
    rcases h with ⟨x, y, hx, hy, h_eq⟩
    have h1 : (x + 1 / y) * (y + 1 / x) ≥ 4 := by
      have h2 : (x + 1 / y) * (y + 1 / x) - 4 ≥ 0 := by
        have h3 : (x + 1 / y) * (y + 1 / x) - 4 = (x * y - 1) ^ 2 / (x * y) := by
          field_simp
          ring
        rw [h3]
        have h4 : x * y > 0 := mul_pos hx hy
        have h5 : (x * y - 1) ^ 2 ≥ 0 := sq_nonneg (x * y - 1)
        have h6 : (x * y - 1) ^ 2 / (x * y) ≥ 0 := by
          apply div_nonneg
          linarith
          linarith
        linarith
      linarith
    -- Now prove z ≥ 8080
    have h20 : (x + 1 / y) * (x + 1 / y + 2018) + (y + 1 / x) * (y + 1 / x + 2018) ≥ 8080 := by
      have h3 : (x + 1 / y) * (x + 1 / y + 2018) + (y + 1 / x) * (y + 1 / x + 2018) =
        (x + 1 / y) ^ 2 + (y + 1 / x) ^ 2 + 2018 * ((x + 1 / y) + (y + 1 / x)) := by 
        ring
      rw [h3]
      have h4 : (x + 1 / y) ^ 2 + (y + 1 / x) ^ 2 ≥ 8 := by
        nlinarith [sq_nonneg ((x + 1 / y) - (y + 1 / x)), sq_nonneg (x * y - 1), 
          sq_nonneg ((x + 1 / x) - 2), sq_nonneg ((y + 1 / y) - 2), h1, mul_pos hx hy
        ]
      have h5 : (x + 1 / y) + (y + 1 / x) ≥ 4 := by
        have h6 : (x + 1 / y) + (y + 1 / x) ≥ 4 := by
          have h7 : (x + 1 / x) ≥ 2 := by 
            have h8 : x + 1 / x - 2 ≥ 0 := by
              have h9 : x + 1 / x - 2 = (x ^ 2 - 2 * x + 1) / x := by
                field_simp
                ring
              rw [h9]
              apply div_nonneg
              · -- Show that the numerator is non-negative
                nlinarith [sq_nonneg (x - 1)]
              · -- Show that the denominator is non-negative
                linarith
            linarith
          have h8 : (y + 1 / y) ≥ 2 := by
            have h9 : y + 1 / y - 2 ≥ 0 := by
              have h10 : y + 1 / y - 2 = (y ^ 2 - 2 * y + 1) / y := by
                field_simp
                ring
              rw [h10]
              apply div_nonneg
              · -- Show that the numerator is non-negative
                nlinarith [sq_nonneg (y - 1)]
              · -- Show that the denominator is non-negative
                linarith
            linarith
          linarith [show (x + 1 / x) ≥ 2 by linarith [h7], show (y + 1 / y) ≥ 2 by linarith [h8], show (x + 1 / y) + (y + 1 / x) = (x + 1 / x) + (y + 1 / y) by ring ]
        linarith
      nlinarith [h4, h5, mul_pos hx hy]
    linarith [h_eq, h20]