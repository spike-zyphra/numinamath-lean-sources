import Mathlib

theorem inequalities_600830 (a b c lambda : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = lambda) :
    5 * lambda^2 / 3 ≤ (a * b^2 + lambda^2 * b) / (c + a) +
      (b * c^2 + lambda^2 * c) / (a + b) +
      (c * a^2 + lambda^2 * a) / (b + c) := by
  have h1 : lambda = a + b + c := by linarith [h]
  rw [h1]
  have ha1 : 0 < c + a := by linarith
  have hb1 : 0 < a + b := by linarith
  have hc1 : 0 < b + c := by linarith
  have h2 : (a * b^2 + (a + b + c)^2 * b) / (c + a) +
    (b * c^2 + (a + b + c)^2 * c) / (a + b) +
    (c * a^2 + (a + b + c)^2 * a) / (b + c) - 5 * (a + b + c)^2 / 3 ≥ 0 := by
    have h3 : (a * b^2 + (a + b + c)^2 * b) / (c + a) +
      (b * c^2 + (a + b + c)^2 * c) / (a + b) +
      (c * a^2 + (a + b + c)^2 * a) / (b + c) - 5 * (a + b + c)^2 / 3 =
        ( (a * b^2 + (a + b + c)^2 * b) * (a + b) * (b + c) +
          (b * c^2 + (a + b + c)^2 * c) * (c + a) * (b + c) +
          (c * a^2 + (a + b + c)^2 * a) * (c + a) * (a + b) - 5 * (a + b + c)^2 / 3 * (c + a) * (a + b) * (b + c) ) / ((c + a) * (a + b) * (b + c)) := by
      field_simp
      ring_nf
    rw [h3]
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
      sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)),
      sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    all_goals
      positivity
  linarith