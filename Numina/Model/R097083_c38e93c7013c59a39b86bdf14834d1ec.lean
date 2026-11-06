import Mathlib

theorem inequalities_48423 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    3 / 4 ≤ a / ((a + 1) * (b + 1)) + b / ((b + 1) * (c + 1)) +
    c / ((c + 1) * (a + 1)) := by
  have h1 : 0 < a * b * c := by nlinarith

  have ha1 : 0 < a + 1 := by linarith
  have hb1 : 0 < b + 1 := by linarith
  have hc1 : 0 < c + 1 := by linarith

  have h2 : a / ((a + 1) * (b + 1)) + b / ((b + 1) * (c + 1)) + c / ((c + 1) * (a + 1)) =
      (a * (c + 1) + b * (a + 1) + c * (b + 1)) / ((a + 1) * (b + 1) * (c + 1)) := by
    field_simp
    <;> ring

  rw [h2]

  have h3 : (a + 1) * (b + 1) * (c + 1) > 0 := by
    positivity

  have h4 : a * (c + 1) + b * (a + 1) + c * (b + 1) >= (3 / 4) * ((a + 1) * (b + 1) * (c + 1)) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          habc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  apply (le_div_iff₀' h3).mpr
  linarith