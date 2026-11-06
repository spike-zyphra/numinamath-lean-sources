import Mathlib

theorem inequalities_599133 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) :
    3 / 4 ≥ 1 / (2 + a^2 + b^2) + 1 / (2 + b^2 + c^2) +
    1 / (2 + c^2 + a^2) := by
  have h1 : 0 < c := hc
  have h2 : 0 < a := ha
  have h3 : 0 < b := hb
  have h4 : a + b + c = 3 := h
  have h5 : a < 3 := by 
    nlinarith
  have h6 : b < 3 := by 
    nlinarith
  have h7 : c < 3 := by 
    nlinarith
  have h10 : 0 < 2 + a^2 + b^2 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb]
  have h11 : 0 < 2 + b^2 + c^2 := by
    nlinarith [sq_pos_of_pos hb, sq_pos_of_pos hc]
  have h12 : 0 < 2 + c^2 + a^2 := by
    nlinarith [sq_pos_of_pos hc, sq_pos_of_pos ha]

  have h8 : 1 / (2 + a^2 + b^2) + 1 / (2 + b^2 + c^2) + 1 / (2 + c^2 + a^2) - 3 / 4 ≤ 0 := by
    have h99 : (1 / (2 + a^2 + b^2) + 1 / (2 + b^2 + c^2) + 1 / (2 + c^2 + a^2) - 3 / 4) =
      (4 * ( (2 + b^2 + c^2) * (2 + c^2 + a^2) ) + 4 * ((2 + a^2 + b^2) * (2 + c^2 + a^2)) + 4 * ((2 + a^2 + b^2) * (2 + b^2 + c^2)) - 3 * (2 + a^2 + b^2) * (2 + b^2 + c^2) * (2 + c^2 + a^2)) / (4 * (2 + a^2 + b^2) * (2 + b^2 + c^2) * (2 + c^2 + a^2)) := by
      field_simp
      ring
    rw [h99]
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show that the numerator is ≤ 0
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
        sq_nonneg (a + b + c - 3), sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), 
        sq_nonneg (c * a - a * b), h, sq_nonneg (a * b + b * c + c * a - 3)]
    · -- Show that the denominator is ≥ 0
      positivity
  linarith
  all_goals
  try positivity
  all_goals
  try nlinarith