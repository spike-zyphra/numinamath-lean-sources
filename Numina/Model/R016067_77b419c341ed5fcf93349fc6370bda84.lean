import Mathlib

theorem inequalities_65439 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    1 / 2 ≤ (a ^ 4 + b ^ 4) / (a ^ 2 + b ^ 2) +
           (b ^ 3 + c ^ 3) / (b + c) +
           (2 * a ^ 2 + b ^ 2 + 2 * c ^ 2) / 2 := by

  have h1 : 0 < a ^ 2 + b ^ 2 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb]

  have h2 : 0 < b + c := by
    nlinarith

  have h4 : (b ^ 3 + c ^ 3) / (b + c) = b ^ 2 - b * c + c ^ 2 := by
    have h5 : b + c ≠ 0 := by
      linarith
    field_simp [h5]
    <;> nlinarith [sq_nonneg (b - c), sq_nonneg (b + c)]
  rw [h4]

  have h8 : c = 1 - a - b := by linarith
  rw [h8]

  -- Now, substitute c =1 -a -b, and prove the inequality.
  have h9 : a + b < 1 := by
    nlinarith

  have h7 : (a ^ 4 + b ^ 4) / (a ^ 2 + b ^ 2) + (b ^ 2 - b * (1 - a - b) + (1 - a - b) ^ 2) + (2 * a ^ 2 + b ^ 2 + 2 * (1 - a - b) ^ 2) / 2 - 1 / 2 ≥ 0 := by

    have pos1 : 0 < a ^ 2 + b ^ 2 := by
      nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb]

    have h7 : (a ^ 4 + b ^ 4) / (a ^ 2 + b ^ 2) + (b ^ 2 - b * (1 - a - b) + (1 - a - b) ^ 2) + (2 * a ^ 2 + b ^ 2 + 2 * (1 - a - b) ^ 2) / 2 - 1 / 2 =
      ((a ^ 4 + b ^ 4) * 2 + (b ^ 2 - b * (1 - a - b) + (1 - a - b) ^ 2) * (a ^ 2 + b ^ 2) * 2 + (2 * a ^ 2 + b ^ 2 + 2 * (1 - a - b) ^ 2) * (a ^ 2 + b ^ 2) - (a ^ 2 + b ^ 2) ) / ((a ^ 2 + b ^ 2) * 2) := by
      field_simp
      <;> ring

    rw [h7] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), 
      sq_nonneg (a * b - a * (1 - a - b)), sq_nonneg (a * b - b * (1 - a - b)), 
      sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a * (a - b)), sq_nonneg (b * (a - b)), 
      mul_pos ha hb, mul_pos ha (show (0 : ℝ) < 1 - a - b by nlinarith), 
      mul_pos hb (show (0 : ℝ) < 1 - a - b by nlinarith), 
      mul_pos ha (show 0 < a * b by nlinarith), 
      mul_pos hb (show 0 < a * b by nlinarith)]

    all_goals positivity

  linarith