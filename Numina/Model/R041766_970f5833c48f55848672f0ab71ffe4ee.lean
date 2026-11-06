import Mathlib

theorem inequalities_76661 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 / (a ^ 2 + 1) + 1 / (b ^ 2 + 1) + 1 / (c ^ 2 + 1) = 2) :
    a * b + a * c + b * c ≤ 3 / 2 := by
  have h1 : 0 < a * b := by
    apply mul_pos
    exact ha
    exact hb

  have h2 : 0 < a * c := by
    apply mul_pos
    exact ha
    exact hc

  have h3 : 0 < b * c := by
    apply mul_pos
    exact hb
    exact hc
  have h4 : 1 / (a ^ 2 + 1) + 1 / (b ^ 2 + 1) + 1 / (c ^ 2 + 1) = 2 := h
  have h5 : (b^2 + 1) * (c^2 + 1) + (a^2 + 1) * (c^2 + 1) + (a^2 + 1) * (b^2 + 1) = 2 * (a^2 + 1) * (b^2 + 1) * (c^2 + 1) := by
    have h6 : a^2 + 1 > 0 := by
      nlinarith [sq_pos_of_pos ha]
    have h7 : b^2 + 1 > 0 := by
      nlinarith [sq_pos_of_pos hb]
    have h8 : c^2 + 1 > 0 := by
      nlinarith [sq_pos_of_pos hc]
    field_simp at h4 ⊢
    nlinarith [h4, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
    sq_nonneg (a * b - 1 / 2), sq_nonneg (a * c - 1 / 2), sq_nonneg (b * c - 1 / 2), 
    mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
  ]