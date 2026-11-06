import Mathlib

theorem algebra_12704 : IsLeast {x | ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 4 * a + b = a * b * c ∧ x = a + b + c} 6 := by
  constructor
  · -- Let's prove that 6 is in the set
    use 1, 2, 3
    norm_num
  · -- Let's prove that for all x in the set, 6 ≤ x
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h1, h2⟩
    have h3 : a + b + c ≥ 6 := by
      have h4 : a * (1 / a) = 1 := by
        field_simp
      have h5 : a + 1 / a ≥ 2 := by
        have h6 : a > 0 := ha
        have h7 : a + 1 / a - 2 ≥ 0 := by
          have h8 : a + 1 / a - 2 = (a - 1) ^ 2 / a := by
            field_simp
            ring
          rw [h8]
          apply div_nonneg
          · -- Show (a - 1) ^ 2 ≥ 0
            apply pow_two_nonneg
          · -- Show a > 0
            linarith
        linarith
      have h8 : b + 4 / b ≥ 4 := by
        have h9 : b > 0 := hb
        have h10 : b + 4 / b - 4 ≥ 0 := by
          have h11 : b + 4 / b - 4 = (b - 2) ^ 2 / b := by
            field_simp
            ring
          rw [h11]
          apply div_nonneg
          · -- Show (b - 2) ^ 2 ≥ 0
            apply pow_two_nonneg
          · -- Show b > 0
            linarith
        linarith
      have h9 : a + b + c = (a + 1 / a) + (b + 4 / b) := by
        have h10 : c = (4 * a + b) / (a * b) := by
          field_simp [(show a * b ≠ 0 by positivity)]
          nlinarith
        rw [h10]
        field_simp [(show a * b ≠ 0 by positivity)]
        ring
      linarith [h5, h8, h9]
    linarith [h2, h3]