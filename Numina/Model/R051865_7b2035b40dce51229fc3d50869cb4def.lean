import Mathlib

theorem inequalities_99997 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : a^2 / (b^2 + c^2) < b^2 / (c^2 + a^2)) (h2 : b^2 / (c^2 + a^2) < c^2 / (a^2 + b^2)) :
    |a| < |b| ∧ |b| < |c| := by

  have pos1 : b^2 + c^2 > 0 := by
    have hb2 : b^2 > 0 := by
      apply sq_pos_of_ne_zero
      exact hb
    have hc2 : c^2 > 0 := by
      apply sq_pos_of_ne_zero
      exact hc
    nlinarith

  have pos2 : c^2 + a^2 > 0 := by
    have hc2 : c^2 > 0 := by
      apply sq_pos_of_ne_zero
      exact hc
    have ha2 : a^2 > 0 := by
      apply sq_pos_of_ne_zero
      exact ha
    nlinarith

  have pos3 : a^2 + b^2 > 0 := by
    have ha2 : a^2 > 0 := by
      apply sq_pos_of_ne_zero
      exact ha
    have hb2 : b^2 > 0 := by
      apply sq_pos_of_ne_zero
      exact hb
    nlinarith

  have h1' : a^2 * (c^2 + a^2) < b^2 * (b^2 + c^2) := by
    apply (div_lt_div_iff (by positivity) (by positivity)).mp at h1
    nlinarith

  have h2' : b^2 * (a^2 + b^2) < c^2 * (c^2 + a^2) := by
    apply (div_lt_div_iff (by positivity) (by positivity)).mp at h2
    nlinarith

  have h3 : a^2 < b^2 := by
    nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (c^2), sq_nonneg (a^2 + b^2 + c^2), sq_pos_of_ne_zero (show a ≠ 0 by assumption), sq_pos_of_ne_zero (show b ≠ 0 by assumption), sq_pos_of_ne_zero (show c ≠ 0 by assumption)]

  have h4 : b^2 < c^2 := by
    nlinarith [sq_nonneg (b^2 - c^2), sq_nonneg (a^2), sq_nonneg (a^2 + b^2 + c^2), sq_pos_of_ne_zero (show a ≠ 0 by assumption), sq_pos_of_ne_zero (show b ≠ 0 by assumption), sq_pos_of_ne_zero (show c ≠ 0 by assumption)]

  have h5 : |a| < |b| := by
    apply sq_lt_sq.mp
    nlinarith

  have h7 : |b| < |c| := by
    apply sq_lt_sq.mp
    nlinarith

  constructor
  · exact h5
  · exact h7