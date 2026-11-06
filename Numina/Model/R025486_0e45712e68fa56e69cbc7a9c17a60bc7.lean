import Mathlib

open Real
open scoped BigOperators

theorem inequalities_275002 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a^2 + b^2 > 5 * c^2) (h1 : a + b > c) (h2 : a + c > b) (h3 : b + c > a) :
  min (min a b) c = c := by
  have h4 : c ≤ a := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h5 : c ≤ b := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h7 : c ≤ a := h4
  have h8 : c ≤ b := h5
  have h9 : min (min a b) c = c := by
    have h13 : c ≤ min a b := by
      cases min_cases a b with
      | inl h14 =>
        nlinarith
      | inr h15 =>
        nlinarith
    have h14 : min (min a b) c = c := by
      rw [min_eq_right]
      all_goals linarith
    exact h14
  exact h9