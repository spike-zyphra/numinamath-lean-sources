import Mathlib

open Real

theorem inequalities_308991 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (2 * sqrt (b ^ 2 - b * c + c ^ 2) + 3 * a) +
    b / (2 * sqrt (c ^ 2 - c * a + a ^ 2) + 3 * b) +
    c / (2 * sqrt (a ^ 2 - a * b + b ^ 2) + 3 * c) ≤ 3 / 5 := by

  have h1 : ∀ x y : ℝ, x > 0 → y > 0 → 2 * sqrt (x ^ 2 - x * y + y ^ 2) ≥ x + y := by
    intro x y hx hy
    have h11 : sqrt (x ^ 2 - x * y + y ^ 2) ≥ (x + y) / 2 := by
      have h12 : (x ^ 2 - x * y + y ^ 2 : ℝ) ≥ ((x + y) / 2) ^ 2 := by
        nlinarith [sq_nonneg (x - y)]
      have h13 : sqrt (x ^ 2 - x * y + y ^ 2) ≥ sqrt (((x + y) / 2) ^ 2) := by
        apply Real.sqrt_le_sqrt
        linarith
      have h14 : sqrt (((x + y) / 2) ^ 2) = (x + y) / 2 := by
        rw [Real.sqrt_sq (by linarith)]
      linarith
    linarith
  have h2 : 2 * sqrt (b ^ 2 - b * c + c ^ 2) ≥ b + c := by
    apply h1 b c hb hc
  have h3 : 2 * sqrt (c ^ 2 - c * a + a ^ 2) ≥ c + a := by
    apply h1 c a hc ha
  have h4 : 2 * sqrt (a ^ 2 - a * b + b ^ 2) ≥ a + b := by
    apply h1 a b ha hb

  have h5 : a / (2 * sqrt (b ^ 2 - b * c + c ^ 2) + 3 * a) ≤ a / (b + c + 3 * a) := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [h2]
  have h6 : b / (2 * sqrt (c ^ 2 - c * a + a ^ 2) + 3 * b) ≤ b / (c + a + 3 * b) := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [h3]
  have h7 : c / (2 * sqrt (a ^ 2 - a * b + b ^ 2) + 3 * c) ≤ c / (a + b + 3 * c) := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [h4]

  have h8 : a / (b + c + 3 * a) + b / (c + a + 3 * b) + c / (a + b + 3 * c) ≤ 3 / 5 := by
    have h81 : 0 < (b + c + 3 * a) * (c + a + 3 * b) * (a + b + 3 * c) := by
      positivity
    have h82 : a / (b + c + 3 * a) + b / (c + a + 3 * b) + c / (a + b + 3 * c) - 3 / 5 ≤ 0 := by
      have h83 : a / (b + c + 3 * a) + b / (c + a + 3 * b) + c / (a + b + 3 * c) - 3 / 5 =
          (5 * a * (c + a + 3 * b) * (a + b + 3 * c) + 5 * b * (b + c + 3 * a) * (a + b + 3 * c) + 5 * c * (b + c + 3 * a) * (c + a + 3 * b) - 3 * (b + c + 3 * a) * (c + a + 3 * b) * (a + b + 3 * c)) / (5 * (b + c + 3 * a) * (c + a + 3 * b) * (a + b + 3 * c)) := by
        field_simp
        ring
      rw [h83]
      apply div_nonpos_of_nonpos_of_nonneg
      · -- Show that the numerator is ≤ 0
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
          sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
      · -- Show that the denominator is ≥ 0
        positivity
    linarith
  linarith [h5, h6, h7, h8]