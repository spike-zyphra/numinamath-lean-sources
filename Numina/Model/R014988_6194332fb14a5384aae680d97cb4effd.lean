import Mathlib

theorem inequalities_8529 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a ^ 2 - a * b) / (b + c) + (b ^ 2 - b * c) / (c + a) + (c ^ 2 - c * a) / (a + b) ≥
    1 / 3 * (a ^ 2 - a * b + b ^ 2 - b * c + c ^ 2 - c * a) * (1 / (b + c) + 1 / (c + a) + 1 / (a + b)) := by
  have h1 : 0 < b + c := by linarith
  have h2 : 0 < c + a := by linarith
  have h3 : 0 < a + b := by linarith
  have h4 : (a ^ 2 - a * b) / (b + c) + (b ^ 2 - b * c) / (c + a) + (c ^ 2 - c * a) / (a + b) - 
    (1 / 3 * (a ^ 2 - a * b + b ^ 2 - b * c + c ^ 2 - c * a) * (1 / (b + c) + 1 / (c + a) + 1 / (a + b))) ≥ 0 := by
    have h5 : (a ^ 2 - a * b) / (b + c) + (b ^ 2 - b * c) / (c + a) + (c ^ 2 - c * a) / (a + b) - 
      (1 / 3 * (a ^ 2 - a * b + b ^ 2 - b * c + c ^ 2 - c * a) * (1 / (b + c) + 1 / (c + a) + 1 / (a + b))) =
      ((a ^ 2 - a * b) * (c + a) * (a + b) + (b ^ 2 - b * c) * (b + c) * (a + b) + (c ^ 2 - c * a) * (b + c) * (c + a) - 
      (1 / 3 * (a ^ 2 - a * b + b ^ 2 - b * c + c ^ 2 - c * a) * ((c + a) * (a + b) + (b + c) * (a + b) + (b + c) * (c + a)))) / ((b + c) * (c + a) * (a + b)) := by
      field_simp
      <;> ring
      <;> field_simp
      <;> ring
    rw [h5]
    have h6 : ((a ^ 2 - a * b) * (c + a) * (a + b) + (b ^ 2 - b * c) * (b + c) * (a + b) + (c ^ 2 - c * a) * (b + c) * (c + a) - 
      (1 / 3 * (a ^ 2 - a * b + b ^ 2 - b * c + c ^ 2 - c * a) * ((c + a) * (a + b) + (b + c) * (a + b) + (b + c) * (c + a)))) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    have h7 : (b + c) * (c + a) * (a + b) > 0 := by positivity
    positivity
  linarith