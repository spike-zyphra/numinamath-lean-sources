import Mathlib

theorem inequalities_178792 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a + b + c ≤ (a^2 + b^2) / (2 * c) + (a^2 + c^2) / (2 * b) + (b^2 + c^2) / (2 * a) ∧
    (a^2 + b^2) / (2 * c) + (a^2 + c^2) / (2 * b) + (b^2 + c^2) / (2 * a) ≤
    (a^3 / (b * c) + b^3 / (a * c) + c^3 / (a * b)) := by
  constructor
  · -- First inequality: a + b + c ≤ (a^2 + b^2) / (2 * c) + (a^2 + c^2) / (2 * b) + (b^2 + c^2) / (2 * a)
    have h1 : 0 < a * b * c := by
      positivity
    have h2 : a + b + c - ((a^2 + b^2) / (2 * c) + (a^2 + c^2) / (2 * b) + (b^2 + c^2) / (2 * a)) ≤ 0 := by
      have h3 : 0 < a := ha
      have h4 : 0 < b := hb
      have h5 : 0 < c := hc
      have h6 : 0 < 2 * a * b * c := by positivity
      have h7 : a + b + c - ((a^2 + b^2) / (2 * c) + (a^2 + c^2) / (2 * b) + (b^2 + c^2) / (2 * a)) =
          (2 * a * b * c * (a + b + c) - (a * b * (a^2 + b^2) + a * c * (a^2 + c^2) + b * c * (b^2 + c^2))) / (2 * a * b * c) := by
        field_simp
        ring
      rw [h7] at *
      apply div_nonpos_of_nonpos_of_nonneg
      · -- Show that the numerator is ≤ 0
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
          sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
        ]
      · -- Show that the denominator is ≥ 0
        positivity
    linarith
  · -- Second inequality: (a^2 + b^2) / (2 * c) + (a^2 + c^2) / (2 * b) + (b^2 + c^2) / (2 * a) ≤ (a^3 / (b * c) + b^3 / (a * c) + c^3 / (a * b))
    have h1 : 0 < a * b * c := by
      positivity
    have h2 : (a^2 + b^2) / (2 * c) + (a^2 + c^2) / (2 * b) + (b^2 + c^2) / (2 * a) - (a^3 / (b * c) + b^3 / (a * c) + c^3 / (a * b)) ≤ 0 := by
      have h3 : 0 < a := ha
      have h4 : 0 < b := hb
      have h5 : 0 < c := hc
      have h6 : 0 < a * b * c := by positivity
      have h7 : (a^2 + b^2) / (2 * c) + (a^2 + c^2) / (2 * b) + (b^2 + c^2) / (2 * a) - (a^3 / (b * c) + b^3 / (a * c) + c^3 / (a * b)) =
          ( (a * b * (a^2 + b^2) + a * c * (a^2 + c^2) + b * c * (b^2 + c^2)) / 2 - (a^4 + b^4 + c^4) ) / (a * b * c) := by
        field_simp
        ring
      rw [h7] at *
      apply div_nonpos_of_nonpos_of_nonneg
      · -- Show that the numerator is ≤ 0
        nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - c^2), sq_nonneg (b^2 - c^2),
          sq_nonneg (a^2 - b * c), sq_nonneg (b^2 - a * c), sq_nonneg (c^2 - a * b),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
        ]
      · -- Show that the denominator is ≥ 0
        positivity
    linarith