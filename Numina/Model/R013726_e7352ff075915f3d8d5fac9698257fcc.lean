import Mathlib


theorem inequalities_108283 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    (a + 1 / b) ^ 2 + (b + 1 / c) ^ 2 + (c + 1 / a) ^ 2 ≥ 3 * (a + b + c + 1) := by
  have h1 : 0 < a * b * c := by
    positivity
  have h2 : a * b * c = 1 := habc

  have h3 : (a + 1 / b) ^ 2 + (b + 1 / c) ^ 2 + (c + 1 / a) ^ 2 - 3 * (a + b + c + 1) ≥ 0 := by
    have h4 : (a + 1 / b) ^ 2 + (b + 1 / c) ^ 2 + (c + 1 / a) ^ 2 - 3 * (a + b + c + 1) =
        ( (a ^ 2 + b ^ 2 + c ^ 2) * (a * b * c) ^ 2 + 2 * (a ^ 3 * b * c ^ 2 + a ^ 2 * b ^ 3 * c + a * b ^ 2 * c ^ 3) + (a ^ 2 * c ^ 2 + a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2) - 3 * (a + b + c + 1) * (a * b * c) ^ 2 ) / ( (a * b * c) ^ 2 ) := by
      field_simp
      ring
    rw [h4]
    have h5 : (a * b * c) ^ 2 > 0 := by
      positivity

    have h7 : ( (a ^ 2 + b ^ 2 + c ^ 2) * (a * b * c) ^ 2 + 2 * (a ^ 3 * b * c ^ 2 + a ^ 2 * b ^ 3 * c + a * b ^ 2 * c ^ 3) + (a ^ 2 * c ^ 2 + a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2) - 3 * (a + b + c + 1) * (a * b * c) ^ 2 ) ≥ 0 := by
      have h1 : a * b * c = 1 := habc
      have h8 : (a * b * c) ^ 2 = 1 := by
        nlinarith [h1]
      rw [h8]
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1)]
    apply div_nonneg
    linarith
    positivity

  linarith