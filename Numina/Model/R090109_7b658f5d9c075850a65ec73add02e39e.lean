import Mathlib

open Real

theorem inequalities_315510 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a ≤ b + c ∧ b + c ≤ 3 * a) (h2 : 3 * b^2 ≤ a * (a + c) ∧ a * (a + c) ≤ 5 * b^2) :
    (b - 2 * c) / a ≥ -18 / 5 := by
  have h3 : a ≤ b + c := h1.1
  have h4 : b + c ≤ 3 * a := h1.2
  have h5 : 3 * b ^ 2 ≤ a * (a + c) := h2.1
  have h6 : a * (a + c) ≤ 5 * b ^ 2 := h2.2
  have ha1 : a > 0 := ha
  have h : b - 2 * c ≥ -18 / 5 * a := by
    nlinarith [sq_nonneg (b - 2 * c), sq_nonneg (a - 5 * b / 4), sq_nonneg (c - 11 * b / 4), sq_nonneg (b - c / 2), sq_nonneg (b + c - 3 * a), sq_nonneg (a * (a + c) - 5 * b^2), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h2 : (b - 2 * c) / a ≥ -18 / 5 := by
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  exact h2