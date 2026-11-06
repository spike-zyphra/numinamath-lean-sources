import Mathlib

theorem algebra_244872 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h : a + b + c = 1) (h1 : 1 / a + 1 / b + 1 / c = 3) (h2 : 1 / a + 1 / b + 1 / c + 1 / d = 4)
    (h3 : 1 / a + 1 / b + 1 / c + 1 / d + 1 / e = 6) :
    ∑ i ∈ Finset.range 4, (1 / a + 1 / b + 1 / c + 1 / d + 1 / e) = 25 := by
  have eq1 : a * b + a * c + b * c = 3 * (a * b * c) := by
    have h1' : 1 / a + 1 / b + 1 / c = 3 := h1
    have h_abc : a * b * c > 0 := by
      apply mul_pos
      apply mul_pos
      exact ha
      exact hb
      exact hc
    field_simp [ha.ne.symm, hb.ne.symm, hc.ne.symm] at h1' ⊢
    nlinarith
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
    mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]