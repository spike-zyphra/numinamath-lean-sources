import Mathlib

theorem inequalities_597820 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / a^2 + 1 / b^2 + 1 / c^2 + 1 / (a + b + c)^2 ≥
    7 / 25 * ((1 / a + 1 / b + 1 / c + 1 / (a + b + c))^2) := by
  have h1 : 0 < a * b * c * (a + b + c) := by
    positivity
  have h2 : a > 0 := by linarith
  have h3 : b > 0 := by linarith
  have h4 : c > 0 := by linarith
  have h5 : a + b + c > 0 := by linarith
  have h6 : a * b * c > 0 := by positivity
  have h7 : a * b > 0 := by positivity
  have h8 : a * c > 0 := by positivity
  have h9 : b * c > 0 := by positivity
  have h10 : a * b * c * (a + b + c) > 0 := by positivity
  have h12 : a ^ 2 * b ^ 2 * c ^ 2 * (a + b + c) ^ 2 > 0 := by positivity
  have h13 : 1 / a^2 + 1 / b^2 + 1 / c^2 + 1 / (a + b + c)^2 - 7 / 25 * ((1 / a + 1 / b + 1 / c + 1 / (a + b + c))^2) ≥ 0 := by
    have h14 : 1 / a^2 + 1 / b^2 + 1 / c^2 + 1 / (a + b + c)^2 - 7 / 25 * ((1 / a + 1 / b + 1 / c + 1 / (a + b + c))^2) =
        ( (b^2 * c^2 * (a + b + c)^2 + a^2 * c^2 * (a + b + c)^2 + a^2 * b^2 * (a + b + c)^2 + a^2 * b^2 * c^2) - (7 / 25) * ( (b * c * (a + b + c) + a * c * (a + b + c) + a * b * (a + b + c) + a * b * c )^2 ) ) / (a ^ 2 * b ^ 2 * c ^ 2 * (a + b + c) ^ 2) := by
      field_simp
      <;> ring_nf
      <;> field_simp
      <;> ring
    rw [h14]
    have h15 : (b^2 * c^2 * (a + b + c)^2 + a^2 * c^2 * (a + b + c)^2 + a^2 * b^2 * (a + b + c)^2 + a^2 * b^2 * c^2) - (7 / 25) * ( (b * c * (a + b + c) + a * c * (a + b + c) + a * b * (a + b + c) + a * b * c )^2 ) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b) + b * (b - c) + c * (c - a)),
        mul_pos ha hb,
        mul_pos hb hc,
        mul_pos ha hc,
        sq_nonneg (a * b * c),
        sq_nonneg (a * b * (a + b + c)),
        sq_nonneg (a * c * (a + b + c)),
        sq_nonneg (b * c * (a + b + c)),
        sq_nonneg ((a + b + c) * (a * b - b * c)),
        sq_nonneg ((a + b + c) * (b * c - c * a)),
        sq_nonneg ((a + b + c) * (c * a - a * b))
      ]
    apply div_nonneg
    linarith
    positivity
  linarith