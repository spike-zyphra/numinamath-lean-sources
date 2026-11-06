import Mathlib

theorem inequalities_7680 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a = 3) :
    (2 * b / (c * (a + b)) + 2 * c / (a * (b + c)) + 2 * a / (b * (c + a))) ≥ ((b + c) / (c * (a + b)) + (c + a) / (a * (b + c)) + (a + b) / (b * (c + a))) := by
  have pos1 : 0 < c * (a + b) := by positivity
  have pos2 : 0 < a * (b + c) := by positivity
  have pos3 : 0 < b * (c + a) := by positivity
  have h2 : (2 * b / (c * (a + b)) + 2 * c / (a * (b + c)) + 2 * a / (b * (c + a))) - ((b + c) / (c * (a + b)) + (c + a) / (a * (b + c)) + (a + b) / (b * (c + a))) ≥ 0 := by
    have h3 : (2 * b / (c * (a + b)) + 2 * c / (a * (b + c)) + 2 * a / (b * (c + a))) - ((b + c) / (c * (a + b)) + (c + a) / (a * (b + c)) + (a + b) / (b * (c + a))) =
        (b - c) / (c * (a + b)) + (c - a) / (a * (b + c)) + (a - b) / (b * (c + a)) := by
      field_simp
      ring
    rw [h3]
    have h4 : (b - c) / (c * (a + b)) + (c - a) / (a * (b + c)) + (a - b) / (b * (c + a)) ≥ 0 := by
      have pos1 : 0 < c * (a + b) := by positivity
      have pos2 : 0 < a * (b + c) := by positivity
      have pos3 : 0 < b * (c + a) := by positivity
      have h5 : (b - c) / (c * (a + b)) + (c - a) / (a * (b + c)) + (a - b) / (b * (c + a)) =
        ((b - c) * (a * (b + c) * b * (c + a)) + (c - a) * (c * (a + b) * b * (c + a)) + (a - b) * (c * (a + b) * a * (b + c))) / (c * (a + b) * a * (b + c) * b * (c + a)) := by
        field_simp
        <;> ring
      rw [h5]
      apply div_nonneg
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
        mul_pos (show 0 < a * b by positivity) (show 0 < b * c by positivity), 
        mul_pos (show 0 < a * b by positivity) (show 0 < c * a by positivity), 
        mul_pos (show 0 < b * c by positivity) (show 0 < c * a by positivity),
        h]
      positivity
    linarith
  linarith