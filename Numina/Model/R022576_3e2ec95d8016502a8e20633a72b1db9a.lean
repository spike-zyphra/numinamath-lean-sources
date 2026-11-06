import Mathlib

theorem inequalities_66478 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 8) :
    (a - 2) / (a + 1) + (b - 2) / (b + 1) + (c - 2) / (c + 1) ≤ 0 := by
  have h1 : 0 < a * b * c := by
    positivity
  have h2 : a + 1 > 0 := by linarith
  have h3 : b + 1 > 0 := by linarith
  have h4 : c + 1 > 0 := by linarith
  have h5 : (a - 2) / (a + 1) + (b - 2) / (b + 1) + (c - 2) / (c + 1) = 
    ((a - 2) * (b + 1) * (c + 1) + (b - 2) * (a + 1) * (c + 1) + (c - 2) * (a + 1) * (b + 1)) / ((a + 1) * (b + 1) * (c + 1)) := by
    field_simp
    ring
  rw [h5] at *
  have h6 : (a - 2) * (b + 1) * (c + 1) + (b - 2) * (a + 1) * (c + 1) + (c - 2) * (a + 1) * (b + 1) ≤ 0 := by
    nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (c - 2),
      sq_nonneg (a * b - 4), sq_nonneg (b * c - 4), sq_nonneg (a * c - 4),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, habc]
  have h7 : (a + 1) * (b + 1) * (c + 1) > 0 := by
    positivity
  apply div_nonpos_of_nonpos_of_nonneg
  · linarith [h6]
  · -- Show that (a + 1) * (b + 1) * (c + 1) ≥ 0
    all_goals
      positivity