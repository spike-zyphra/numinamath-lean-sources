import Mathlib

theorem inequalities_3054
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    a ^ 2 / (a + 1) ^ 2 + b ^ 2 / (b + 1) ^ 2 + c ^ 2 / (c + 1) ^ 2 +
    1 / 4 * (1 / a + 1 / b + 1 / c) ≥ 3 / 2 := by
  have h1 : a ^ 2 / (a + 1) ^ 2 + 1 / 4 / a - 1 / 2 ≥ 0 := by
    have h6 : 0 < a := ha
    have h7 : a ^ 2 / (a + 1) ^ 2 + 1 / 4 / a - 1 / 2 ≥ 0 := by
      have h8 : a ^ 2 / (a + 1) ^ 2 + 1 / 4 / a - 1 / 2 = (4 * a^3 + (a + 1) ^ 2 - 2 * a * (a + 1) ^ 2) / (4 * a * (a + 1) ^ 2) := by
        field_simp
        ring
      rw [h8] at *
      apply div_nonneg
      -- Prove 0 ≤ Numerator
      nlinarith [sq_nonneg (a - 1), sq_nonneg (a), sq_nonneg (a * (a - 1)), sq_nonneg (a * (a * (a - 1))), sq_nonneg (a + 1 / 2), sq_nonneg (a - 1 / 2), sq_nonneg (a * (a - 1 / 2)), mul_pos ha (show 0 < a by linarith), mul_pos ha (show 0 < a + 1 by linarith)]
      -- Prove 0 ≤ Denominator
      positivity
    linarith
  have h2 : b ^ 2 / (b + 1) ^ 2 + 1 / 4 / b - 1 / 2 ≥ 0 := by
    have h6 : 0 < b := hb
    have h7 : b ^ 2 / (b + 1) ^ 2 + 1 / 4 / b - 1 / 2 ≥ 0 := by
      have h8 : b ^ 2 / (b + 1) ^ 2 + 1 / 4 / b - 1 / 2 = (4 * b^3 + (b + 1) ^ 2 - 2 * b * (b + 1) ^ 2) / (4 * b * (b + 1) ^ 2) := by
        field_simp
        ring
      rw [h8] at *
      apply div_nonneg
      -- Prove 0 ≤ Numerator
      nlinarith [sq_nonneg (b - 1), sq_nonneg (b), sq_nonneg (b * (b - 1)), sq_nonneg (b * (b * (b - 1))), sq_nonneg (b + 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (b * (b - 1 / 2)), mul_pos hb (show 0 < b by linarith), mul_pos hb (show 0 < b + 1 by linarith)]
      -- Prove 0 ≤ Denominator
      positivity
    linarith
  have h3 : c ^ 2 / (c + 1) ^ 2 + 1 / 4 / c - 1 / 2 ≥ 0 := by
    have h6 : 0 < c := hc
    have h7 : c ^ 2 / (c + 1) ^ 2 + 1 / 4 / c - 1 / 2 ≥ 0 := by
      have h8 : c ^ 2 / (c + 1) ^ 2 + 1 / 4 / c - 1 / 2 = (4 * c^3 + (c + 1) ^ 2 - 2 * c * (c + 1) ^ 2) / (4 * c * (c + 1) ^ 2) := by
        field_simp
        ring
      rw [h8] at *
      apply div_nonneg
      -- Prove 0 ≤ Numerator
      nlinarith [sq_nonneg (c - 1), sq_nonneg (c), sq_nonneg (c * (c - 1)), sq_nonneg (c * (c * (c - 1))), sq_nonneg (c + 1 / 2), sq_nonneg (c - 1 / 2), sq_nonneg (c * (c - 1 / 2)), mul_pos hc (show 0 < c by linarith), mul_pos hc (show 0 < c + 1 by linarith)]
      -- Prove 0 ≤ Denominator
      positivity
    linarith
  have h4 : a ^ 2 / (a + 1) ^ 2 + 1 / 4 / a ≥ 1 / 2 := by linarith [h1]
  have h5 : b ^ 2 / (b + 1) ^ 2 + 1 / 4 / b ≥ 1 / 2 := by linarith [h2]
  have h6 : c ^ 2 / (c + 1) ^ 2 + 1 / 4 / c ≥ 1 / 2 := by linarith [h3]
  have h7 : a ^ 2 / (a + 1) ^ 2 + b ^ 2 / (b + 1) ^ 2 + c ^ 2 / (c + 1) ^ 2 + 1 / 4 * (1 / a + 1 / b + 1 / c) ≥ 3 / 2 := by
    have eq2 : a ^ 2 / (a + 1) ^ 2 + b ^ 2 / (b + 1) ^ 2 + c ^ 2 / (c + 1) ^ 2 + 1 / 4 * (1 / a + 1 / b + 1 / c) =
        (a ^ 2 / (a + 1) ^ 2 + 1 / 4 / a) + (b ^ 2 / (b + 1) ^ 2 + 1 / 4 / b) + (c ^ 2 / (c + 1) ^ 2 + 1 / 4 / c) := by
      field_simp
      <;> ring
    rw [eq2]
    linarith [h4, h5, h6]
  exact h7