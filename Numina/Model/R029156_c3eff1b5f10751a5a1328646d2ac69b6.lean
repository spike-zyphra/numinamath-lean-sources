import Mathlib

theorem inequalities_71900 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a * b * c * d = 1) :
    1 ≤ 1 / (1 + a)^2 + 1 / (1 + b)^2 + 1 / (1 + c)^2 + 1 / (1 + d)^2 := by
  have h1 : 0 < a * b := by
    nlinarith
  -- We will prove that $\frac{1}{(1 + a)^2} + \frac{1}{(1 + b)^2} \geq \frac{1}{1 + a \cdot b}$
  have h2 : 1 / (1 + a) ^ 2 + 1 / (1 + b) ^ 2 ≥ 1 / (1 + a * b) := by
    have h3 : 0 < (1 + a) ^ 2 * (1 + b) ^ 2 * (1 + a * b) := by
      positivity
    have h4 : 1 / (1 + a) ^ 2 + 1 / (1 + b) ^ 2 - 1 / (1 + a * b) ≥ 0 := by
      have h5 : 1 / (1 + a) ^ 2 + 1 / (1 + b) ^ 2 - 1 / (1 + a * b) =
          ((1 + b) ^ 2 * (1 + a * b) + (1 + a) ^ 2 * (1 + a * b) - (1 + a) ^ 2 * (1 + b) ^ 2) / ((1 + a) ^ 2 * (1 + b) ^ 2 * (1 + a * b)) := by
        field_simp
        <;> ring
      rw [h5]
      apply div_nonneg
      nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a - b), sq_nonneg (a - 1), sq_nonneg (b - 1),
        mul_pos ha hb
      ]
      all_goals positivity
    linarith
  have h3 : 0 < c * d := by
    nlinarith
  -- Similarly for the second pair
  have h4 : 1 / (1 + c) ^ 2 + 1 / (1 + d) ^ 2 ≥ 1 / (1 + c * d) := by
    have h5 : 0 < (1 + c) ^ 2 * (1 + d) ^ 2 * (1 + c * d) := by
      positivity
    have h6 : 1 / (1 + c) ^ 2 + 1 / (1 + d) ^ 2 - 1 / (1 + c * d) ≥ 0 := by
      have h7 : 1 / (1 + c) ^ 2 + 1 / (1 + d) ^ 2 - 1 / (1 + c * d) =
          ((1 + d) ^ 2 * (1 + c * d) + (1 + c) ^ 2 * (1 + c * d) - (1 + c) ^ 2 * (1 + d) ^ 2) / ((1 + c) ^ 2 * (1 + d) ^ 2 * (1 + c * d)) := by
        field_simp
        <;> ring
      rw [h7]
      apply div_nonneg
      nlinarith [sq_nonneg (c * d - 1), sq_nonneg (c - d), sq_nonneg (c - 1), sq_nonneg (d - 1),
        mul_pos hc hd
      ]
      all_goals positivity
    linarith
  -- Now we can show that $\frac{1}{1 + a \cdot b} + \frac{1}{1 + c \cdot d} = 1$
  have h5 : 1 / (1 + a * b) + 1 / (1 + c * d) = 1 := by
    have h6 : c * d = 1 / (a * b) := by
      have h7 : a * b ≠ 0 := by
        nlinarith
      field_simp at *
      nlinarith
      all_goals nlinarith
    rw [h6]
    field_simp [(show a * b ≠ 0 by positivity)]
    <;> nlinarith
  -- The final inequality
  linarith [h2, h4, h5]