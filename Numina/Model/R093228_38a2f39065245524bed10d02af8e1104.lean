import Mathlib

theorem inequalities_597980 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 ≤ 1 / (1 + 2 * a) + 1 / (1 + 2 * b) + 1 / (1 + 2 * c) := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    · apply mul_pos ha hb
    · exact hc
  have h2 : a * b * c = 1 := habc
  have ha1 : 0 < 1 + 2 * a := by linarith
  have hb1 : 0 < 1 + 2 * b := by linarith
  have hc1 : 0 < 1 + 2 * c := by linarith
  have h : 1 / (1 + 2 * a) + 1 / (1 + 2 * b) + 1 / (1 + 2 * c) - 1 ≥ 0 := by
    have h3 : (1 / (1 + 2 * a) + 1 / (1 + 2 * b) + 1 / (1 + 2 * c) - 1) =
        ((1 + 2 * b) * (1 + 2 * c) + (1 + 2 * a) * (1 + 2 * c) + (1 + 2 * a) * (1 + 2 * b) - (1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c)) / ((1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c)) := by
      field_simp
      ring
    rw [h3]
    have h4 : (1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c) > 0 := by
      positivity
    have h5 : (1 + 2 * b) * (1 + 2 * c) + (1 + 2 * a) * (1 + 2 * c) + (1 + 2 * a) * (1 + 2 * b) - (1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, habc, mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith), mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ c by linarith), mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ c by linarith)]
    apply div_nonneg
    · linarith
    · nlinarith
  linarith