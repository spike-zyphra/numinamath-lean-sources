import Mathlib

theorem inequalities_99903
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h : a^3 + b^3 + c^3 = a * b + b * c + c * a) :
    a + b + c ≤ 3 ∧ a^3 + b^3 + c^3 ≤ 3 := by
  have h1 : a^3 + b^3 + c^3 = a * b + b * c + c * a := h
  have h2 : (a - b)^2 + (a - c)^2 + (b - c)^2 ≥ 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  -- Prove a + b + c ≤ 3
  have h3 : a + b + c ≤ 3 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  -- Prove a^3 + b^3 + c^3 ≤ 3
  have h4 : a^3 + b^3 + c^3 ≤ 3 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  exact ⟨h3, h4⟩