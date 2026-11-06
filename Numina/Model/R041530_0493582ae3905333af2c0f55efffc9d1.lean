import Mathlib

theorem algebra_178386 (x : ℝ) (hx : x ≥ 11) :
    Real.sqrt ((x - 3) / 11) + Real.sqrt ((x - 4) / 10) + Real.sqrt ((x - 5) / 9) =
    Real.sqrt ((x - 11) / 3) + Real.sqrt ((x - 10) / 4) + Real.sqrt ((x - 9) / 5) ↔ x = 14 := by
  constructor
  · -- Assume the equation holds, prove x = 14
    intro h_eq
    have h1 : Real.sqrt ((x - 3) / 11) ≥ 0 := Real.sqrt_nonneg ((x - 3) / 11)
    have h2 : Real.sqrt ((x - 4) / 10) ≥ 0 := Real.sqrt_nonneg ((x - 4) / 10)
    have h3 : Real.sqrt ((x - 5) / 9) ≥ 0 := Real.sqrt_nonneg ((x - 5) / 9)
    have h4 : Real.sqrt ((x - 11) / 3) ≥ 0 := Real.sqrt_nonneg ((x - 11) / 3)
    have h5 : Real.sqrt ((x - 10) / 4) ≥ 0 := Real.sqrt_nonneg ((x - 10) / 4)
    have h6 : Real.sqrt ((x - 9) / 5) ≥ 0 := Real.sqrt_nonneg ((x - 9) / 5)
    by_cases h7 : x > 14
    · -- Let's prove a contradiction
      have h8 : Real.sqrt ((x - 3) / 11) < Real.sqrt ((x - 11) / 3) := by
        apply Real.sqrt_lt_sqrt
        · -- Show (x - 3) / 11 ≥ 0
          linarith
        · -- Show (x - 3) / 11 < (x - 11) / 3
          have h9 : x > 14 := h7
          have h10 : (x - 3) / 11 < (x - 11) / 3 := by
            have h4 : x > 14 := h9
            nlinarith
          linarith
      have h9 : Real.sqrt ((x - 4) / 10) < Real.sqrt ((x - 10) / 4) := by
        apply Real.sqrt_lt_sqrt
        · -- Show (x - 4) / 10 ≥ 0
          linarith
        · -- Show (x - 4) / 10 < (x - 10) / 4
          have h9 : x > 14 := h7
          have h11 : (x - 4) / 10 < (x - 10) / 4 := by
            have h4 : x > 14 := h9
            nlinarith
          linarith
      have h10 : Real.sqrt ((x - 5) / 9) < Real.sqrt ((x - 9) / 5) := by
        apply Real.sqrt_lt_sqrt
        · -- Show (x - 5) / 9 ≥ 0
          linarith
        · -- Show (x - 5) / 9 < (x - 9) / 5
          have h9 : x > 14 := h7
          have h12 : (x - 5) / 9 < (x - 9) / 5 := by
            have h4 : x > 14 := h9
            nlinarith
          linarith
      have h8' : Real.sqrt ((x - 3) / 11) + Real.sqrt ((x - 4) / 10) + Real.sqrt ((x - 5) / 9) < 
          Real.sqrt ((x - 11) / 3) + Real.sqrt ((x - 10) / 4) + Real.sqrt ((x - 9) / 5) := by
        linarith [h8, h9, h10, h1, h2, h3, h4, h5, h6]
      linarith [h8', h_eq]
    by_cases h7 : x < 14
    · -- Let's prove a contradiction
      have h8 : Real.sqrt ((x - 3) / 11) > Real.sqrt ((x - 11) / 3) := by
        apply Real.sqrt_lt_sqrt
        · -- Show (x - 11) / 3 ≥ 0
          linarith
        · -- Show (x - 11) / 3 < (x - 3) / 11
          have h9 : x < 14 := h7
          have h10 : (x - 11) / 3 < (x - 3) / 11 := by
            nlinarith
          linarith
      have h9 : Real.sqrt ((x - 4) / 10) > Real.sqrt ((x - 10) / 4) := by
        apply Real.sqrt_lt_sqrt
        · -- Show (x - 10) / 4 ≥ 0
          linarith
        · -- Show (x - 10) / 4 < (x - 4) / 10
          have h9 : x < 14 := h7
          have h11 : (x - 10) / 4 < (x - 4) / 10 := by
            nlinarith
          linarith
      have h10 : Real.sqrt ((x - 5) / 9) > Real.sqrt ((x - 9) / 5) := by
        apply Real.sqrt_lt_sqrt
        · -- Show (x - 9) / 5 ≥ 0
          linarith
        · -- Show (x - 9) / 5 < (x - 5) / 9
          have h9 : x < 14 := h7
          have h12 : (x - 9) / 5 < (x - 5) / 9 := by
            nlinarith
          linarith
      have  h8' : Real.sqrt ((x - 3) / 11) + Real.sqrt ((x - 4) / 10) + Real.sqrt ((x - 5) / 9) > 
          Real.sqrt ((x - 11) / 3) + Real.sqrt ((x - 10) / 4) + Real.sqrt ((x - 9) / 5) := by
        linarith [h8, h9, h10, h1, h2, h3, h4, h5, h6]
      linarith [h8', h_eq]
    linarith
  · -- Assume x = 14 prove the equation
    intro h_eq
    rw [h_eq]
    have h1 : Real.sqrt ((14 - 3 : ℝ) / 11) = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : Real.sqrt ((14 - 4 : ℝ) / 10) = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h3 : Real.sqrt ((14 - 5 : ℝ) / 9) = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h4 : Real.sqrt ((14 - 11 : ℝ) / 3) = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h5 : Real.sqrt ((14 - 10 : ℝ) / 4) = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h6 : Real.sqrt ((14 - 9 : ℝ) / 5) = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2, h3, h4, h5, h6]
    all_goals linarith