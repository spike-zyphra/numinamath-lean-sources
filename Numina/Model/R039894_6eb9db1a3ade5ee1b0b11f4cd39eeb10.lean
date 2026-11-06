import Mathlib

theorem algebra_178182 (x : ℝ) (hx : x ≥ 2 ∧ x ≥ 3 ∧ x ≥ 4 ∧ x ≥ 11 ∧ x ≥ 10 ∧ x ≥ 9 ∧ x ≥ 1) :
    Real.sqrt ((x - 2) / 11) + Real.sqrt ((x - 3) / 10) + Real.sqrt ((x - 4) / 9) =
    Real.sqrt ((x - 11) / 2) + Real.sqrt ((x - 10) / 3) + Real.sqrt ((x - 9) / 4) ↔ x = 13 := by
  constructor
  · -- Forward implication: if the equation holds, then x = 13.
    intro h
    rcases hx with ⟨h2, h3, h4, h11, h10, h9, h1⟩
    by_cases h' : x > 13
    · -- Case x > 13
      have h14 : Real.sqrt ((x - 2) / 11) < Real.sqrt ((x - 11) / 2) := by
        have h6 : (x - 2) / 11 < (x - 11) / 2 := by
          nlinarith
        have h110 : (x - 2) / 11 ≥ 0 := by
          nlinarith
        have h111 : (x - 11) / 2 ≥ 0 := by
          nlinarith
        apply Real.sqrt_lt_sqrt
        all_goals
          nlinarith
      have h15 : Real.sqrt ((x - 3) / 10) < Real.sqrt ((x - 10) / 3) := by
        have h7 : (x - 3) / 10 < (x - 10) / 3 := by
          nlinarith
        have h110 : (x - 3) / 10 ≥ 0 := by
          nlinarith
        have h111 : (x - 10) / 3 ≥ 0 := by
          nlinarith
        apply Real.sqrt_lt_sqrt
        all_goals
          nlinarith
      have h16 : Real.sqrt ((x - 4) / 9) < Real.sqrt ((x - 9) / 4) := by
        have h8 : (x - 4) / 9 < (x - 9) / 4 := by
          nlinarith
        have h110 : (x - 4) / 9 ≥ 0 := by
          nlinarith
        have h111 : (x - 9) / 4 ≥ 0 := by
          nlinarith
        apply Real.sqrt_lt_sqrt
        all_goals
          nlinarith
      have h17 : Real.sqrt ((x - 2) / 11) + Real.sqrt ((x - 3) / 10) + Real.sqrt ((x - 4) / 9) < 
        Real.sqrt ((x - 11) / 2) + Real.sqrt ((x - 10) / 3) + Real.sqrt ((x - 9) / 4) := by
        linarith
      linarith
    · -- Case x ≤ 13
      by_cases h'' : x < 13
      · -- Case x < 13
        have h18 : Real.sqrt ((x - 2) / 11) > Real.sqrt ((x - 11) / 2) := by
          have h9 : (x - 2) / 11 > (x - 11) / 2 := by
            nlinarith
          have h110 : (x - 2) / 11 ≥ 0 := by
            nlinarith
          have h111 : (x - 11) / 2 ≥ 0 := by
            nlinarith
          apply Real.sqrt_lt_sqrt
          all_goals
            nlinarith
        have h19 : Real.sqrt ((x - 3) / 10) > Real.sqrt ((x - 10) / 3) := by
          have h10 : (x - 3) / 10 > (x - 10) / 3 := by
            nlinarith
          have h110 : (x - 3) / 10 ≥ 0 := by
            nlinarith
          have h111 : (x - 10) / 3 ≥ 0 := by
            nlinarith
          apply Real.sqrt_lt_sqrt
          all_goals
            nlinarith
        have h20 : Real.sqrt ((x - 4) / 9) > Real.sqrt ((x - 9) / 4) := by
          have h11 : (x - 4) / 9 > (x - 9) / 4 := by
            nlinarith
          have h110 : (x - 4) / 9 ≥ 0 := by
            nlinarith
          have h111 : (x - 9) / 4 ≥ 0 := by
            nlinarith
          apply Real.sqrt_lt_sqrt
          all_goals
            nlinarith
        have h21 : Real.sqrt ((x - 2) / 11) + Real.sqrt ((x - 3) / 10) + Real.sqrt ((x - 4) / 9) > 
          Real.sqrt ((x - 11) / 2) + Real.sqrt ((x - 10) / 3) + Real.sqrt ((x - 9) / 4) := by
          linarith
        linarith
      · -- Case x = 13
        have h'' : x = 13 := by
          linarith
        tauto
  · -- Backward implication: if x = 13, then the equation holds.
    intro h
    rw [show x = 13 by linarith [h]]
    have h90 : Real.sqrt ((13 - 2: ℝ) / 11) = 1 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    have h91 : Real.sqrt ((13 - 3: ℝ) / 10) = 1 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    have h92 : Real.sqrt ((13 - 4: ℝ) / 9) = 1 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    have h103 : Real.sqrt ((13 - 11: ℝ) / 2) = 1 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    have h104 : Real.sqrt ((13 - 10: ℝ) / 3) = 1 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    have h105 : Real.sqrt ((13 - 9: ℝ) / 4) = 1 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    rw [h90, h91, h92, h103, h104, h105]
    all_goals
      norm_num