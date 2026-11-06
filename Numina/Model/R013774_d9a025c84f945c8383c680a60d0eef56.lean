import Mathlib

theorem inequalities_598643 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a * b + b * c + c * a = 1) :
    5 / 2 ≤ 1 / (a + b) + 1 / (b + c) + 1 / (c + a) := by
  -- Show that denominators are all positive.
  have h1 : a + b > 0 := by
    by_contra h1
    push_neg at h1
    have ha0 : a = 0 := by linarith [h1, ha]
    have hb0 : b = 0 := by linarith [h1, hb]
    rw [ha0, hb0] at h
    nlinarith [hc, h]
  -- Show that denominators are all positive.
  have h2 : b + c > 0 := by
    by_contra h2
    push_neg at h2
    have hb0 : b = 0 := by linarith [h2, hb]
    have hc0 : c = 0 := by linarith [h2, hc]
    rw [hb0, hc0] at h
    nlinarith [ha, h]
  -- Show that denominators are all positive.
  have h3 : c + a > 0 := by
    by_contra h3
    push_neg at h3
    have hc0 : c = 0 := by linarith [h3, hc]
    have ha0 : a = 0 := by linarith [h3, ha]
    rw [hc0, ha0] at h
    nlinarith [hb, h]
  have h4 : 1 / (a + b) + 1 / (b + c) + 1 / (c + a) - 5 / 2 ≥ 0 := by
    have pos1 : 0 < (a + b) * (b + c) * (c + a) := by positivity
    have eq1 : 1 / (a + b) + 1 / (b + c) + 1 / (c + a) - 5 / 2 =
        ((b + c) * (c + a) + (a + b) * (c + a) + (a + b) * (b + c) - (5 / 2) * (a + b) * (b + c) * (c + a)) / ((a + b) * (b + c) * (c + a)) := by
      field_simp [show a + b ≠ 0 by linarith, show b + c ≠ 0 by linarith, show c + a ≠ 0 by linarith]
      ring
    rw [eq1]
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
              sq_nonneg (a + b + c - 2), sq_nonneg (a * b + b * c + c * a - 1),
              mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc, h]
    positivity
  linarith