import Mathlib

theorem inequalities_261898 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a + b + c ≤ (a ^ 4 + b ^ 4 + c ^ 4) / (a * b * c) := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc

  have h3 : a^4 + b^4 + c^4 ≥ a^2 * b * c + a * b^2 * c + a * b * c^2 := by
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  have h4 : (a + b + c) * (a * b * c) ≤ (a ^ 4 + b ^ 4 + c ^ 4) := by
    nlinarith [h3]

  have h5 : a + b + c ≤ (a ^ 4 + b ^ 4 + c ^ 4) / (a * b * c) := by
    apply (le_div_iff₀ (by positivity)).mpr
    linarith [h4]

  exact h5