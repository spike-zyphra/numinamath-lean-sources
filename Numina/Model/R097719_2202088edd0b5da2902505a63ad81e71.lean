import Mathlib

theorem inequalities_129233 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a ≤ b + c) (h2 : b + c ≤ 3 * a) (h3 : 3 * b^2 ≤ a * (a + c)) (h4 : a * (a + c) ≤ 5 * b^2) :
    (b - 2 * c) / a ≥ -18 / 5 := by
  have h5 : b - 2 * c ≥ -18 / 5 * a := by
    nlinarith [sq_nonneg (a - 3 * b / 2),
      sq_nonneg (c - (3 * a - b) / 2),
      sq_nonneg (a - 2 * b),
      sq_nonneg (c - (a - b) / 2),
      mul_pos ha hb,
      mul_pos hb hc,
      mul_pos ha hc]
  have h6 : (b - 2 * c) / a ≥ -18 / 5 := by
    apply (le_div_iff₀' (by positivity)).mpr
    linarith [h5]
  exact h6