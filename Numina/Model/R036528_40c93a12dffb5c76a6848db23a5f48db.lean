import Mathlib

theorem inequalities_176771 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hprod : a * b * c = 1) (hsum : a + b + c > 1 / a + 1 / b + 1 / c) :
    (a > 1 ∧ b ≤ 1 ∧ c ≤ 1) ∨ (b > 1 ∧ a ≤ 1 ∧ c ≤ 1) ∨ (c > 1 ∧ a ≤ 1 ∧ b ≤ 1) := by

  have h1 : 0 < a * b * c := by
    positivity

  have h2 : 1 / a + 1 / b + 1 / c = (b * c + a * c + a * b) / (a * b * c) := by
    field_simp
    <;> ring

  rw [h2, hprod] at hsum

  have h3 : a + b + c - (b * c + a * c + a * b) > 0 := by
    linarith

  by_cases ha1 : a > 1
  · -- Assume a > 1
    have h4 : b ≤ 1 := by
      nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, hprod, mul_self_nonneg (a - 1), mul_self_nonneg (b - 1), mul_self_nonneg (c - 1)]

    have h5 : c ≤ 1 := by
      nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, hprod, mul_self_nonneg (a - 1), mul_self_nonneg (b - 1), mul_self_nonneg (c - 1)]

    left
    constructor
    · exact ha1
    constructor
    · exact h4
    · exact h5

  · -- Assume a ≤ 1
    by_cases hb1 : b > 1
    · -- Assume b > 1
      have h6 : a ≤ 1 := by
        linarith

      have h7 : c ≤ 1 := by
        nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, hprod, mul_self_nonneg (a - 1), mul_self_nonneg (b - 1), mul_self_nonneg (c - 1)]

      right
      left
      constructor
      · exact hb1
      constructor
      · exact h6
      · exact h7

    · -- Assume neither a > 1 nor b > 1.
      have h8 : a ≤ 1 := by linarith
      have h9 : b ≤ 1 := by linarith

      have h10 : c > 1 := by
        nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, hprod, mul_self_nonneg (a - 1), mul_self_nonneg (b - 1), mul_self_nonneg (c - 1)]

      right
      right
      constructor
      · exact h10
      constructor
      · exact h8
      · exact h9