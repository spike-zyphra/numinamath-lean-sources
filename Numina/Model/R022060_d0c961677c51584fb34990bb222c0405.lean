import Mathlib

theorem inequalities_1088 (a b c : ℝ) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
  a ^ 2 / (b - c) ^ 2 + b ^ 2 / (c - a) ^ 2 + c ^ 2 / (a - b) ^ 2 ≥ 2 := by
  have h1 : a - b ≠ 0 := by
    intro h
    apply hab
    linarith
  have h2 : b - c ≠ 0 := by
    intro h
    apply hbc
    linarith
  have h3 : c - a ≠ 0 := by
    intro h
    apply hca
    linarith
  have h4 : 0 < (b - c) ^ 2 := by
    apply sq_pos_of_ne_zero
    exact h2
  have h5 : 0 < (c - a) ^ 2 := by
    apply sq_pos_of_ne_zero
    exact h3
  have h6 : 0 < (a - b) ^ 2 := by
    apply sq_pos_of_ne_zero
    exact h1
  have h7 : a ^ 2 / (b - c) ^ 2 + b ^ 2 / (c - a) ^ 2 + c ^ 2 / (a - b) ^ 2 - 2 ≥ 0 := by
    have h8 : a ^ 2 / (b - c) ^ 2 + b ^ 2 / (c - a) ^ 2 + c ^ 2 / (a - b) ^ 2 - 2 =
        ( (a ^ 2 * (c - a) ^ 2 * (a - b) ^ 2 + b ^ 2 * (b - c) ^ 2 * (a - b) ^ 2 + c ^ 2 * (b - c) ^ 2 * (c - a) ^ 2 - 2 * (b - c) ^ 2 * (c - a) ^ 2 * (a - b) ^ 2) ) / ( (b - c) ^ 2 * (c - a) ^ 2 * (a - b) ^ 2 ) := by
      field_simp
      ring
    rw [h8]
    have h9 : (a ^ 2 * (c - a) ^ 2 * (a - b) ^ 2 + b ^ 2 * (b - c) ^ 2 * (a - b) ^ 2 + c ^ 2 * (b - c) ^ 2 * (c - a) ^ 2 - 2 * (b - c) ^ 2 * (c - a) ^ 2 * (a - b) ^ 2 ) ≥ 0 := by
      nlinarith [sq_nonneg (a * (c - a) * (a - b) - b * (b - c) * (a - b)), sq_nonneg (b * (b - c) * (a - b) - c * (b - c) * (c - a)), sq_nonneg (c * (b - c) * (c - a) - a * (c - a) * (a - b)), sq_nonneg (a * (b - c) + b * (c - a) + c * (a - b)), sq_nonneg (a * (c - a) * (a - b) + b * (b - c) * (a - b) + c * (b - c) * (c - a)), sq_nonneg (a * (b - c) * (c - a)), sq_nonneg (b * (c - a) * (a - b)), sq_nonneg (c * (a - b) * (b - c)), sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b)]
    apply div_nonneg
    linarith
    all_goals
      positivity
  linarith