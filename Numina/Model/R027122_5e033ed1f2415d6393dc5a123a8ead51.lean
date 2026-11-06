import Mathlib

open Real

theorem inequalities_315144 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) :
    ((a + 3)^2 / (2 * a^2 + (3 - a)^2) +
     (b + 3)^2 / (2 * b^2 + (3 - b)^2) +
     (c + 3)^2 / (2 * c^2 + (3 - c)^2)) ≤ 8 := by
  have h1 : c = 3 - a - b := by linarith
  rw [show c = 3 - a - b by linarith]
  have pos1 : 0 < (2 * a^2 + (3 - a) ^ 2 : ℝ) := by
    nlinarith [sq_nonneg (a - 1)]
  have pos2 : 0 < (2 * b^2 + (3 - b) ^ 2 : ℝ) := by 
    nlinarith [sq_nonneg (b - 1)]
  have pos3 : 0 < (2 * (3 - a - b) ^ 2 + (3 - (3 - a - b)) ^ 2 : ℝ) := by
    nlinarith [sq_nonneg (3 - a - b - 1)]
  have h6 : ((a + 3)^2 / (2 * a^2 + (3 - a) ^ 2) +
      (b + 3)^2 / (2 * b^2 + (3 - b) ^ 2) +
      ( (3 - a - b) + 3) ^ 2 / (2 * (3 - a - b) ^ 2 + (3 - (3 - a - b)) ^ 2) ) - 8 ≤ 0 := by
    have pos1' : 0 < (2 * a^2 + (3 - a) ^ 2 : ℝ) := pos1
    have pos2' : 0 < (2 * b^2 + (3 - b) ^ 2 : ℝ) := pos2
    have pos3' : 0 < (2 * (3 - a - b) ^ 2 + (3 - (3 - a - b)) ^ 2 : ℝ) := pos3
    have h7 : ((a + 3)^2 / (2 * a^2 + (3 - a) ^ 2) +
        (b + 3)^2 / (2 * b^2 + (3 - b) ^ 2) +
        ( (3 - a - b) + 3) ^ 2 / (2 * (3 - a - b) ^ 2 + (3 - (3 - a - b)) ^ 2) ) - 8 =
        ((a + 3) ^ 2 * (2 * b^2 + (3 - b) ^ 2) * (2 * (3 - a - b) ^ 2 + (3 - (3 - a - b)) ^ 2) +
        (b + 3) ^ 2 * (2 * a^2 + (3 - a) ^ 2) * (2 * (3 - a - b) ^ 2 + (3 - (3 - a - b)) ^ 2) +
        ( (3 - a - b) + 3) ^ 2 * (2 * a^2 + (3 - a) ^ 2) * (2 * b^2 + (3 - b) ^ 2) - 8 * (2 * a^2 + (3 - a) ^ 2) * (2 * b^2 + (3 - b) ^ 2) * (2 * (3 - a - b) ^ 2 + (3 - (3 - a - b)) ^ 2)) / ((2 * a^2 + (3 - a) ^ 2) * (2 * b^2 + (3 - b) ^ 2) * (2 * (3 - a - b) ^ 2 + (3 - (3 - a - b)) ^ 2)) := by 
      field_simp
      <;> ring
    rw [h7] at *
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Prove the numerator is ≤ 0
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - (3 - a - b)), sq_nonneg (b - (3 - a - b)), 
        sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg ((3 - a - b) - 1), 
        sq_nonneg (a * b - b * (3 - a - b)), sq_nonneg (b * (3 - a - b) - a * (3 - a - b)), 
        mul_pos ha hb, 
        mul_pos ha (show 0 < (3 - a - b : ℝ) by nlinarith), 
        mul_pos hb (show 0 < (3 - a - b : ℝ) by nlinarith), 
        sq_nonneg (a + b - (3 - a - b)), 
        sq_nonneg (a - b + (3 - a - b)), 
        sq_nonneg ((a - 1) * (b - 1)), 
        sq_nonneg ((a - 1) * ((3 - a - b) - 1)), 
        sq_nonneg ((b - 1) * ((3 - a - b) - 1))
      ]
    · -- Prove the denominator is ≥ 0
      positivity
  linarith