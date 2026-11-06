import Mathlib

open BigOperators Real Set

theorem algebra_111070 :
  IsLeast {x | ∃ a b : ℝ, b ≠ 0 ∧ x = 2*a^2 + b^2 + 2*a*(1 - b) + 1 / b^2 + 1 / b *(2*a + 2) + 1} (1 / 2) := by
  constructor
  · -- Show 1/2 is in the set
    use -1/2, -1
    norm_num
  · -- Show 1/2 is the least element in the set
    intro x hx
    rcases hx with ⟨a, b, hb, heq⟩
    have heq2 : 2 * a ^ 2 + b ^ 2 + 2 * a * (1 - b) + 1 / b ^ 2 + 1 / b * (2 * a + 2) + 1 =
        2 * (a + (1 - b) / 2 + 1 / (2 * b)) ^ 2 + 1 / 2 * (b + 1 / b + 1) ^ 2 := by
      have hb' : b ≠ 0 := hb
      field_simp [hb']
      ring
    have heq3 : x = 2 * (a + (1 - b) / 2 + 1 / (2 * b)) ^ 2 + 1 / 2 * (b + 1 / b + 1) ^ 2 := by
      linarith [heq, heq2]
    have h1 : b + 1 / b ≥ 2 ∨ b + 1 / b ≤ -2 := by
      by_cases hb1 : b > 0
      · -- Case where b > 0.
        have h1 : b + 1 / b ≥ 2 := by
          have h2 : b + 1 / b - 2 ≥ 0 := by
            have h3 : b + 1 / b - 2 = (b ^ 2 + 1 - 2 * b) / b := by 
              field_simp
              <;> ring
            rw [h3]
            apply div_nonneg
            · -- Show numerator ≥ 0.
              have h4 : b ^ 2 - 2 * b + 1 ≥ 0 := by
                have h5 : b ^ 2 - 2 * b + 1 = (b - 1) ^ 2 := by ring
                rw [h5]
                positivity
              nlinarith
            · -- Show denominator ≥ 0.
              linarith [hb1]
          linarith
        left
        linarith
      · -- Case where b ≤ 0.
        have hb2 : b ≤ 0 := by linarith
        have hb3 : b < 0 := by
          by_contra h
          push_neg at h
          have : b = 0 := by linarith [hb2, h]
          tauto
        have hb4 : b + 1 / b ≤ -2 := by
          have h1 : b + 1 / b + 2 ≤ 0 := by
            have h2 : b + 1 / b + 2 = (b ^ 2 + 1 + 2 * b) / b := by
              field_simp
              <;> ring
            rw [h2]
            apply div_nonpos_of_nonneg_of_nonpos
            · -- Show numerator ≥ 0.
              have h3 : b ^ 2 + 2 * b + 1 ≥ 0 := by
                have h4 : b ^ 2 + 2 * b + 1 = (b + 1) ^ 2 := by ring
                rw [h4]
                positivity
              nlinarith
            · -- Show denominator ≤ 0.
              nlinarith
          nlinarith
        right
        linarith
    have h11 : (b + 1 / b + 1) ^ 2 ≥ 1 := by
      cases h1 with
      | inl h3 =>
        nlinarith [sq_nonneg (b + 1 / b + 1 - 3)]
      | inr h3 =>
        nlinarith [sq_nonneg (b + 1 / b + 1)]
    have h12 : 1 / 2 * (b + 1 / b + 1) ^ 2 ≥ 1 / 2 := by
      nlinarith
    have h21 : 2 * (a + (1 - b) / 2 + 1 / (2 * b)) ^ 2 ≥ 0 := by
      positivity
    have hx1 : x ≥ 1 / 2 := by
      nlinarith
    linarith