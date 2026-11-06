import Mathlib

theorem inequalities_6979 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 * (a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c) ^ 2 - 1 ≤
    (a - b) ^ 2 / ((b + c) * (c + a)) +
    (b - c) ^ 2 / ((c + a) * (a + b)) +
    (c - a) ^ 2 / ((a + b) * (b + c)) := by

  have h2 : (a - b) ^ 2 / ((b + c) * (c + a)) +
      (b - c) ^ 2 / ((c + a) * (a + b)) +
      (c - a) ^ 2 / ((a + b) * (b + c)) =
      ((a - b) ^ 2 * (a + b) + (b - c) ^ 2 * (b + c) + (c - a) ^ 2 * (c + a)) / ((b + c) * (c + a) * (a + b)) := by
    field_simp
    ring

  have h3 : 3 * (a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c) ^ 2 - 1 =
      (3 * (a ^ 2 + b ^ 2 + c ^ 2) - (a + b + c) ^ 2) / (a + b + c) ^ 2 := by
    field_simp
    <;> ring
  rw [h2, h3]

  have pos1 : 0 < (a + b + c) ^ 2 := by
    positivity
  have pos2 : 0 < (b + c) * (c + a) * (a + b) := by
    positivity
  have h5 : ((a - b) ^ 2 * (a + b) + (b - c) ^ 2 * (b + c) + (c - a) ^ 2 * (c + a)) / ((b + c) * (c + a) * (a + b)) ≥ (3 * (a ^ 2 + b ^ 2 + c ^ 2) - (a + b + c) ^ 2) / (a + b + c) ^ 2 := by
    have pos3 : 0 < (a + b + c) ^ 2 * ((b + c) * (c + a) * (a + b)) := by
      positivity
    have h4' : ((a - b) ^ 2 * (a + b) + (b - c) ^ 2 * (b + c) + (c - a) ^ 2 * (c + a)) / ((b + c) * (c + a) * (a + b)) - (3 * (a ^ 2 + b ^ 2 + c ^ 2) - (a + b + c) ^ 2) / (a + b + c) ^ 2 ≥ 0 := by
      have pos4 : 0 < (a + b + c) ^ 2 * ((b + c) * (c + a) * (a + b)) := by
        positivity
      have h5' : ((a - b) ^ 2 * (a + b) + (b - c) ^ 2 * (b + c) + (c - a) ^ 2 * (c + a)) / ((b + c) * (c + a) * (a + b)) - (3 * (a ^ 2 + b ^ 2 + c ^ 2) - (a + b + c) ^ 2) / (a + b + c) ^ 2 =
          ((a - b) ^ 2 * (a + b) * (a + b + c) ^ 2 + (b - c) ^ 2 * (b + c) * (a + b + c) ^ 2 + (c - a) ^ 2 * (c + a) * (a + b + c) ^ 2 - ((3 * (a ^ 2 + b ^ 2 + c ^ 2) - (a + b + c) ^ 2) * ((b + c) * (c + a) * (a + b))) ) / ((a + b + c) ^ 2 * ((b + c) * (c + a) * (a + b))) := by
        field_simp
        <;> ring
      rw [h5']
      apply div_nonneg
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
        sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
      ]
      all_goals positivity
    linarith
  linarith [ h5 ]