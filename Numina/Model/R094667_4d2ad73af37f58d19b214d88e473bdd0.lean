import Mathlib

theorem inequalities_108383
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (habc : a * b * c = 1) :
    (a * b + b * c + 1 / c / a) * (b * c + c * a + 1 / a / b) *
    (c * a + a * b + 1 / b / c) ≥ (1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c) := by

  have h1 : (1 / c / a) = b := by
    have h1 : a * b * c = 1 := habc
    field_simp [show a ≠ 0 by linarith, show c ≠ 0 by linarith]
    all_goals nlinarith [habc, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  have h2 : (1 / a / b) = c := by
    have h2 : a * b * c = 1 := habc
    field_simp [show a ≠ 0 by linarith, show b ≠ 0 by linarith]
    all_goals nlinarith [habc, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  have h3 : (1 / b / c) = a := by
    have h3 : a * b * c = 1 := habc
    field_simp [show b ≠ 0 by linarith, show c ≠ 0 by linarith]
    all_goals nlinarith [habc, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    
  have h4 : (a * b + b * c + 1 / c / a) = b * (a + c + 1) := by
    rw [h1]
    ring

  have h5 : (b * c + c * a + 1 / a / b) = c * (a + b + 1) := by
    rw [h2]
    ring

  have h6 : (c * a + a * b + 1 / b / c) = a * (b + c + 1) := by
    rw [h3]
    ring
  
  rw [h4, h5, h6]

  have h7 : (b * (a + c + 1) : ℝ) * (c * (a + b + 1)) * (a * (b + c + 1)) =
    (a + c + 1) * (a + b + 1) * (b + c + 1) * (a * b * c) := by ring
  
  rw [h7, habc]
  
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]