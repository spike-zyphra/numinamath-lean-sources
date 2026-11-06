import Mathlib

open Real

lemma lemma_1 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (Y : ℝ) (hY : Y = (a + 2 * b) ^ 2) :
    (Y - 4 * b ^ 2) * Y < (Y - b ^ 2) ^ 2 := by
  have h1 : 0 < a + 2 * b := by linarith [ha, hb]
  have h2 : 0 < Y := by
    rw [hY]
    positivity
  have h3 : 0 < b ^ 2 := by positivity
  have h4 : 0 < b ^ 4 := by positivity
  have h5 : 0 < 2 * Y + b ^ 2 := by
    rw [hY]
    nlinarith [sq_nonneg (a), sq_nonneg (b), mul_pos ha hb, sq_pos_of_pos ha, sq_pos_of_pos hb, sq_nonneg (a + 2 * b)]
  have h6 : -2 * b ^ 2 * Y - b ^ 4 < 0 := by
    nlinarith [show 0 < b ^ 2 by positivity, show 0 < 2 * Y + b ^ 2 by assumption, sq_pos_of_pos ha, sq_pos_of_pos hb]
  have h7 : (Y - 4 * b ^ 2) * Y < (Y - b ^ 2) ^ 2 := by
    have eq6 : (Y - 4 * b ^ 2) * Y = Y^2 - 4 * b^2 * Y := by
      ring
    have eq7 : (Y - b ^ 2) ^ 2 = Y^2 - 2 * b^2 * Y + b^4 := by
      ring
    have eq8 : (Y - 4 * b ^ 2) * Y < (Y - b ^ 2) ^ 2 := by
      rw [eq6, eq7]
      nlinarith [show 0 < b ^ 2 by positivity, sq_pos_of_pos ha, sq_pos_of_pos hb, sq_nonneg (a + 2 * b), sq_nonneg (a - b), sq_nonneg (a * b), mul_pos ha hb, h6]
    linarith
  exact h7


theorem inequalities_50576 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a / (a + b) * (a + 2 * b) / (a + 3 * b) < sqrt (a / (a + 4 * b)) := by
  have h1 : 0 < a + b := by linarith
  have h2 : 0 < a + 2 * b := by linarith
  have h3 : 0 < a + 3 * b := by linarith
  have h4 : 0 < a + 4 * b := by linarith
  have h5 : 0 < a / (a + b) * (a + 2 * b) / (a + 3 * b) := by
    positivity
  have h9 : (a / (a + b) * (a + 2 * b) / (a + 3 * b)) ^ 2 < a / (a + 4 * b) := by
    have h17 : 0 < a := by linarith
    have h18 : 0 < b := by linarith
    have h22 : 0 < (a + b) ^ 2 * (a + 3 * b) ^ 2 := by positivity
    have h7 : (a / (a + b) * (a + 2 * b) / (a + 3 * b)) ^ 2 = a ^ 2 * (a + 2 * b) ^ 2 / ((a + b) ^ 2 * (a + 3 * b) ^ 2) := by
      field_simp
      <;> ring
    rw [h7]
    have h8 : a ^ 2 * (a + 2 * b) ^ 2 / ((a + b) ^ 2 * (a + 3 * b) ^ 2) < a / (a + 4 * b) := by
      have h9 : 0 < a := by linarith
      have h11 : a ^ 2 * (a + 2 * b) ^ 2 * (a + 4 * b) < a * ((a + b) ^ 2 * (a + 3 * b) ^ 2) := by
        nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_nonneg (a - b), sq_nonneg (a * b), sq_nonneg (a + 2 * b), sq_nonneg (a + 3 * b), sq_pos_of_pos (show 0 < a + b by linarith), sq_pos_of_pos (show 0 < a + 3 * b by linarith), sq_pos_of_pos (show 0 < a + 4 * b by linarith), mul_pos ha hb, mul_pos ha (show 0 < b ^ 2 by positivity), mul_pos hb (show 0 < a ^ 2 by positivity), mul_pos (show 0 < a ^ 2 by positivity) (show 0 < b ^ 2 by positivity), sq_nonneg (a ^ 2 - b ^ 2)]
      have pos1 : 0 < (a + b) ^ 2 * (a + 3 * b) ^ 2 * (a + 4 * b) := by
        positivity
      have h13 : a ^ 2 * (a + 2 * b) ^ 2 / ((a + b) ^ 2 * (a + 3 * b) ^ 2) - a / (a + 4 * b) < 0 := by
        have h14 : a ^ 2 * (a + 2 * b) ^ 2 / ((a + b) ^ 2 * (a + 3 * b) ^ 2) - a / (a + 4 * b) = 
          (a ^ 2 * (a + 2 * b) ^ 2 * (a + 4 * b) - a * ((a + b) ^ 2 * (a + 3 * b) ^ 2)) / ((a + b) ^ 2 * (a + 3 * b) ^ 2 * (a + 4 * b)) := by
          field_simp
          <;> ring
        rw [h14]
        apply div_neg_of_neg_of_pos
        · nlinarith
        · positivity
      linarith
    linarith
  have h61 : a / (a + b) * (a + 2 * b) / (a + 3 * b) < sqrt (a / (a + 4 * b)) := by
    have h71 : 0 ≤ (a / (a + 4 * b) : ℝ) := by positivity
    have h72 : (a / (a + b) * (a + 2 * b) / (a + 3 * b) : ℝ) ^ 2 < (a / (a + 4 * b) : ℝ) := h9
    have h73 : 0 ≤ (a / (a + b) * (a + 2 * b) / (a + 3 * b) : ℝ) := by positivity
    have h74 : (sqrt (a / (a + 4 * b)) : ℝ) ≥ 0 := by positivity
    nlinarith [Real.sqrt_nonneg (a / (a + 4 * b)), Real.sq_sqrt (show 0 ≤ (a / (a + 4 * b) : ℝ) by positivity)]
  exact h61