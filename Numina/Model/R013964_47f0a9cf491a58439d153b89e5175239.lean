import Mathlib

theorem inequalities_598531 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    64 ≤ (1 + 1 / a) * (1 + 1 / b) * (1 + 1 / c) := by

  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith

  have h2 : (1 + 1 / a) * (1 + 1 / b) * (1 + 1 / c) = (a + 1) * (b + 1) * (c + 1) / (a * b * c) := by
    field_simp
    <;> ring

  rw [h2]
  have h3 : (a + 1) * (b + 1) * (c + 1) ≥ 64 * (a * b * c) := by
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  have h4 : (a + 1) * (b + 1) * (c + 1) / (a * b * c) ≥ 64 := by
    have h5 : (a * b * c) > 0 := h1
    apply (le_div_iff₀ (by positivity)).mpr
    linarith [h3]

  linarith [h4]