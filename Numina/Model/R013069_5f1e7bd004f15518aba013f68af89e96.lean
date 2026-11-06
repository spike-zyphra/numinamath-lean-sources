import Mathlib

theorem inequalities_232206 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a + b + c ≤ (a ^ 4 + b ^ 4 + c ^ 4) / (a * b * c) := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h2 : (a + b + c) * (a * b * c) ≤ a ^ 4 + b ^ 4 + c ^ 4 := by
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b) + a * (a - c) + b * (b - c)), sq_nonneg (a * (a - b) + b * (b - a)), sq_nonneg (a * (a - c) + c * (c - a)), sq_nonneg (b * (b - c) + c * (c - b)),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h3 : a * b * c > 0 := h1
  have h4 : a + b + c ≤ (a ^ 4 + b ^ 4 + c ^ 4) / (a * b * c) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  exact h4