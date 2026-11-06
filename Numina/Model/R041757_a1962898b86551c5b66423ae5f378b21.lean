import Mathlib

theorem algebra_242909 {a b c : ℝ} (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c)
    (h : a^2 / (b - c)^2 + b^2 / (c - a)^2 + c^2 / (a - b)^2 = 2) :
    a / (b - c) + b / (c - a) + c / (a - b) = 0 := by

  have h1 : a - b ≠ 0 := by
    intro h1
    apply ha
    linarith

  have h2 : b - c ≠ 0 := by
    intro h2
    apply hb
    linarith

  have h3 : c - a ≠ 0 := by
    intro h3
    apply hc
    linarith

  have h4 : a / (b - c) + b / (c - a) + c / (a - b) = 0 := by
    field_simp [(show b - c ≠ 0 by
      intro h4
      apply hb
      linarith
    ), (show c - a ≠ 0 by
      intro h4
      apply hc
      linarith
    ), (show a - b ≠ 0 by
      intro h4
      apply ha
      linarith
    )] at h ⊢
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr ha), sq_pos_of_ne_zero (sub_ne_zero.mpr hb), sq_pos_of_ne_zero (sub_ne_zero.mpr hc),
      sq_nonneg (a * (c - a) * (a - b) - b * (b - c) * (a - b) + c * (b - c) * (c - a)), sq_nonneg (a * (c - a) - b * (b - c)), sq_nonneg (a * (a - b) - c * (b - c)), sq_nonneg (b * (a - b) - c * (c - a))]
  exact h4