import Mathlib

theorem inequalities_315874 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (b^2 * c^2 + c^2 * a^2 + a^2 * b^2) / (a + b + c) ≥ a * b * c := by
  have h1 : a + b + c > 0 := by
    positivity
  have h2 : b^2 * c^2 + c^2 * a^2 + a^2 * b^2 ≥ a * b * c * (a + b + c) := by
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
          ]
  have h4 : (b^2 * c^2 + c^2 * a^2 + a^2 * b^2) / (a + b + c) ≥ a * b * c := by
    have h5 : a + b + c > 0 := h1
    apply (le_div_iff₀ h5).mpr
    linarith
  exact h4