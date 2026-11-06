import Mathlib

theorem inequalities_117141 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (2 * a + b + c)^2 / (2 * a^2 + (b + c)^2) +
    (2 * b + a + c)^2 / (2 * b^2 + (c + a)^2) +
    (2 * c + a + b)^2 / (2 * c^2 + (a + b)^2) ≤ 8 := by
  have h1 : ∀ x y : ℝ, x > 0 → y > 0 → (x + y) ^ 2 ≤ 4 * (x ^ 2 + y ^ 2) := by
    intros x y hx hy
    nlinarith [sq_nonneg (x - y)]
  have h2 : (2 * a + b + c) ^ 2 ≤ 4 * (2 * a^2 + (b + c) ^ 2) := by
    nlinarith [sq_nonneg (2 * a - (b + c)), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  have h3 : (2 * b + a + c) ^ 2 ≤ 4 * (2 * b^2 + (c + a) ^ 2) := by
    nlinarith [sq_nonneg (2 * b - (c + a)), sq_nonneg (b - a), sq_nonneg (b - c), sq_nonneg (a - c)]
  have h4 : (2 * c + a + b) ^ 2 ≤ 4 * (2 * c^2 + (a + b) ^ 2) := by
    nlinarith [sq_nonneg (2 * c - (a + b)), sq_nonneg (c - a), sq_nonneg (c - b), sq_nonneg (a - b)]
  have h5 : (2 * a + b + c) ^ 2 / (2 * a^2 + (b + c) ^ 2) ≤ 4 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [h2]
  have h6 : (2 * b + a + c) ^ 2 / (2 * b^2 + (c + a) ^ 2) ≤ 4 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [h3]
  have h7 : (2 * c + a + b) ^ 2 / (2 * c^2 + (a + b) ^ 2) ≤ 4 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [h4]
  -- Check that the sum of the fractions is at most 8 by writing them in a complex fraction
  have h8 : (2 * a + b + c) ^ 2 / (2 * a^2 + (b + c) ^ 2) + (2 * b + a + c) ^ 2 / (2 * b^2 + (c + a) ^ 2) + (2 * c + a + b) ^ 2 / (2 * c^2 + (a + b) ^ 2) - 8 ≤ 0 := by
    have h9 : 0 < (2 * a^2 + (b + c) ^ 2) * (2 * b^2 + (c + a) ^ 2) * (2 * c^2 + (a + b) ^ 2) := by positivity
    have h10 : (2 * a + b + c) ^ 2 / (2 * a^2 + (b + c) ^ 2) + (2 * b + a + c) ^ 2 / (2 * b^2 + (c + a) ^ 2) + (2 * c + a + b) ^ 2 / (2 * c^2 + (a + b) ^ 2) - 8 =
        ((2 * a + b + c) ^ 2 * (2 * b^2 + (c + a) ^ 2) * (2 * c^2 + (a + b) ^ 2) +
        (2 * b + a + c) ^ 2 * (2 * a^2 + (b + c) ^ 2) * (2 * c^2 + (a + b) ^ 2) +
        (2 * c + a + b) ^ 2 * (2 * a^2 + (b + c) ^ 2) * (2 * b^2 + (c + a) ^ 2) - 8 * (2 * a^2 + (b + c) ^ 2) * (2 * b^2 + (c + a) ^ 2) * (2 * c^2 + (a + b) ^ 2)) / ((2 * a^2 + (b + c) ^ 2) * (2 * b^2 + (c + a) ^ 2) * (2 * c^2 + (a + b) ^ 2)) := by
      field_simp
      <;> ring
    rw [h10]
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show that the numerator is nonpositive
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
      ]
    · -- Show that the denominator is nonnegative
      positivity
  linarith