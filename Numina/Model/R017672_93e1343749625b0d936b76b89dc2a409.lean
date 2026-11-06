import Mathlib

theorem inequalities_600878 (a b c : ℝ) (h : a ≠ 0 ∨ b ≠ 0) :
    ((a^2 + b^2 + a * c)^2 + (a^2 + b^2 + b * c)^2) / (a^2 + b^2) ≥ (a + b + c)^2 := by
  have h1 : a^2 + b^2 > 0 := by
    by_contra h2
    push_neg at h2
    have h2 : a^2 + b^2 = 0 := by linarith [show a^2 ≥ 0 by positivity, show b^2 ≥ 0 by positivity]
    have h4 : a^2 = 0 := by
      nlinarith [show a^2 ≥ 0 by positivity, show b^2 ≥ 0 by positivity]
    have h5 : b^2 = 0 := by
      nlinarith [show a^2 ≥ 0 by positivity, show b^2 ≥ 0 by positivity]
    have h4 : a = 0 := by
      nlinarith
    have h5 : b = 0 := by
      nlinarith
    cases h with
    | inl h4' =>
      contradiction
    | inr h5' =>
      contradiction
  have h2 : (a^2 + b^2 + a * c)^2 + (a^2 + b^2 + b * c)^2 ≥ (a + b + c) ^ 2 * (a^2 + b^2) := by
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg ((a^2 + b^2) - a * c - b * c), sq_nonneg (a * b), sq_nonneg (c), sq_nonneg (a + b + c), sq_pos_of_pos (show 0 < (2 : ℝ) by norm_num), mul_self_nonneg (a + b - c), mul_self_nonneg (a - b), mul_self_nonneg (a * c - b * c), sq_nonneg (a^2 + b^2 - a * c - b * c)]
  have h3 : ((a ^ 2 + b ^ 2 + a * c) ^ 2 + (a ^ 2 + b ^ 2 + b * c) ^ 2) / (a ^ 2 + b ^ 2) ≥ (a + b + c) ^ 2 := by
    have h4 : a^2 + b^2 > 0 := h1
    apply (le_div_iff₀ h4).mpr
    linarith [h2]
  linarith