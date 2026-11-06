import Mathlib

theorem inequalities_237173 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / a + 1 / b + 1 / c ≥ 2 / (a + b) + 2 / (b + c) + 2 / (c + a) ∧
    2 / (a + b) + 2 / (b + c) + 2 / (c + a) ≥ 9 / (a + b + c) := by
  constructor
  · -- Prove the first inequality.
    have h1 : 1 / a + 1 / b + 1 / c - (2 / (a + b) + 2 / (b + c) + 2 / (c + a)) ≥ 0 := by
      have h11 : a > 0 := by linarith
      have h12 : b > 0 := by linarith
      have h13 : c > 0 := by linarith
      have h21 : a + b > 0 := by linarith
      have h22 : b + c > 0 := by linarith
      have h23 : c + a > 0 := by linarith
      have h31 : a * b * c * (a + b) * (b + c) * (c + a) > 0 := by positivity
      have h41 : (1 / a + 1 / b + 1 / c - (2 / (a + b) + 2 / (b + c) + 2 / (c + a))) =
          (b * c * (a + b) * (b + c) * (c + a) + a * c * (a + b) * (b + c) * (c + a) + a * b * (a + b) * (b + c) * (c + a) - 2 * a * b * c * (b + c) * (c + a) - 2 * a * b * c * (a + b) * (c + a) - 2 * a * b * c * (a + b) * (b + c)) / (a * b * c * (a + b) * (b + c) * (c + a)) := by
        field_simp
        <;> ring
      rw [h41]
      apply div_nonneg
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
        sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
        mul_pos (show 0 < a + b by linarith) (show 0 < b + c by linarith), 
        mul_pos (show 0 < b + c by linarith) (show 0 < c + a by linarith), 
        mul_pos (show 0 < a + b by linarith) (show 0 < c + a by linarith)]
      all_goals positivity
    linarith
  · -- Prove the second inequality.
    have h42 : 2 / (a + b) + 2 / (b + c) + 2 / (c + a) - 9 / (a + b + c) ≥ 0 := by
      have h11 : a > 0 := by linarith
      have h12 : b > 0 := by linarith
      have h13 : c > 0 := by linarith
      have h21 : a + b > 0 := by linarith
      have h22 : b + c > 0 := by linarith
      have h23 : c + a > 0 := by linarith
      have h31 : (a + b) * (b + c) * (c + a) * (a + b + c) > 0 := by positivity
      have h421 : (2 / (a + b) + 2 / (b + c) + 2 / (c + a) - 9 / (a + b + c)) =
          (2 * (b + c) * (c + a) * (a + b + c) + 2 * (a + b) * (c + a) * (a + b + c) + 2 * (a + b) * (b + c) * (a + b + c) - 9 * (a + b) * (b + c) * (c + a)) / ((a + b) * (b + c) * (c + a) * (a + b + c)) := by
        field_simp
        <;> ring
      rw [h421]
      apply div_nonneg
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
        sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
        mul_pos (show 0 < a + b by linarith) (show 0 < b + c by linarith), 
        mul_pos (show 0 < b + c by linarith) (show 0 < c + a by linarith), 
        mul_pos (show 0 < a + b by linarith) (show 0 < c + a by linarith)
      ]
      all_goals positivity
    linarith