import Mathlib

theorem inequalities_108866 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^2 * b * (b - c) / (a + b) + b^2 * c * (c - a) / (b + c) +
    c^2 * a * (a - b) / (c + a) ≥ 0 := by
  have h1 : 0 < a + b := by linarith
  have h2 : 0 < b + c := by linarith
  have h3 : 0 < c + a := by linarith
  have h4 : a + b ≠ 0 := by linarith
  have h5 : b + c ≠ 0 := by linarith
  have h6 : c + a ≠ 0 := by linarith

  have eq1 : a^2 * b * (b - c) / (a + b) + b^2 * c * (c - a) / (b + c) + c^2 * a * (a - b) / (c + a) =
      a^2 * b * (b - c) * (b + c) * (c + a) / ((a + b) * (b + c) * (c + a)) +
      b^2 * c * (c - a) * (a + b) * (c + a) / ((a + b) * (b + c) * (c + a)) +
      c^2 * a * (a - b) * (a + b) * (b + c) / ((a + b) * (b + c) * (c + a)) := by 
    field_simp [h1, h2, h3, h4, h5, h6]
    <;> ring_nf
    <;> field_simp [h1, h2, h3, h4, h5, h6]
    <;> ring

  rw [eq1]

  have eq2 : a^2 * b * (b - c) * (b + c) * (c + a) / ((a + b) * (b + c) * (c + a)) +
      b^2 * c * (c - a) * (a + b) * (c + a) / ((a + b) * (b + c) * (c + a)) +
      c^2 * a * (a - b) * (a + b) * (b + c) / ((a + b) * (b + c) * (c + a)) =
      (a^2 * b * (b - c) * (b + c) * (c + a) + b^2 * c * (c - a) * (a + b) * (c + a) + c^2 * a * (a - b) * (a + b) * (b + c)) / ((a + b) * (b + c) * (c + a)) := by
    ring_nf

  rw [eq2]

  have h7 : 0 < (a + b) * (b + c) * (c + a) := by
    positivity

  apply div_nonneg
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
          sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), 
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  all_goals positivity