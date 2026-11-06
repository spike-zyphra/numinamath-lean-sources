import Mathlib

open Real

theorem inequalities_103656 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : (a^2 + b^2 + c^2)^2 > 2 * (a^4 + b^4 + c^4)) :
    a + b > c ∧ b + c > a ∧ c + a > b := by
  have h1 : a + b > c := by
    by_contra h1
    push_neg at h1
    have h2 : c ≥ a + b := by linarith
    have h3 : c^2 ≥ (a + b) ^ 2 := by nlinarith [sq_nonneg (c - (a + b)), h2, mul_pos ha hb]
    have h4 : (a^2 + b^2 + c^2)^2 ≤ 2 * (a^4 + b^4 + c^4) := by
      nlinarith [sq_nonneg (a + b - c), sq_nonneg (a - b + c), sq_nonneg (-a + b + c),
        sq_nonneg (a^2 + b^2 - c^2), sq_nonneg (a * b - b * c), sq_nonneg (a * b - a * c), sq_nonneg (a * c - b * c),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    linarith

  have h2 : b + c > a := by
    by_contra h2
    push_neg at h2
    have h3 : a ≥ b + c := by linarith
    have h4 : a^2 ≥ (b + c) ^ 2 := by nlinarith [sq_nonneg (a - (b + c)), h3, mul_pos hb hc]
    have h5 : (a^2 + b^2 + c^2)^2 ≤ 2 * (a^4 + b^4 + c^4) := by
      nlinarith [sq_nonneg (a - b - c), sq_nonneg (a + b - c), sq_nonneg (a - b + c), sq_nonneg (-a + b + c),
        sq_nonneg (b^2 + c^2 - a^2), sq_nonneg (a * b - b * c), sq_nonneg (a * b - a * c), sq_nonneg (a * c - b * c),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    linarith

  have h3 : c + a > b := by
    by_contra h3
    push_neg at h3
    have h4 : b ≥ c + a := by linarith
    have h5 : b^2 ≥ (c + a) ^ 2 := by nlinarith [sq_nonneg (b - (c + a)), h4, mul_pos ha hc]
    have h6 : (a^2 + b^2 + c^2)^2 ≤ 2 * (a^4 + b^4 + c^4) := by
      nlinarith [sq_nonneg (a + b - c), sq_nonneg (a - b + c), sq_nonneg (-a + b + c), sq_nonneg (a + b + c),
        sq_nonneg (a^2 + c^2 - b^2), sq_nonneg (a * b - b * c), sq_nonneg (a * b - a * c), sq_nonneg (a * c - b * c),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    linarith

  exact ⟨h1, h2, h3⟩