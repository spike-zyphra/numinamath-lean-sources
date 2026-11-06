import Mathlib

theorem inequalities_603260 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h : a + b = 1) :
    a / (a ^ 2 + b) + b / (a + b ^ 2) ≤ 4 / 3 ∧
    a / (a + b ^ 3) + b / (a ^ 3 + b) ≤ 8 / 5 := by
  constructor
  · -- First part: prove a/(a^2+b) + b/(a+b^2) ≤ 4/3
    have h1 : 0 < a * b := by
      nlinarith
    have h2 : a / (a ^ 2 + b) + b / (a + b ^ 2) - 4 / 3 ≤ 0 := by
      have pos1 : 0 < a ^ 2 + b := by
        nlinarith
      have pos2 : 0 < a + b ^ 2 := by
        nlinarith
      have pos3 : 0 < (a ^ 2 + b) * (a + b ^ 2) := by
        positivity
      have h3 : a / (a ^ 2 + b) + b / (a + b ^ 2) - 4 / 3 =
          (3 * a * (a + b ^ 2) + 3 * b * (a ^ 2 + b) - 4 * (a ^ 2 + b) * (a + b ^ 2)) / (3 * (a ^ 2 + b) * (a + b ^ 2)) := by
        field_simp
        <;> ring
      rw [h3] at *
      have h4 : 3 * a * (a + b ^ 2) + 3 * b * (a ^ 2 + b) - 4 * (a ^ 2 + b) * (a + b ^ 2) ≤ 0 := by
        rw [show b = 1 - a by linarith]
        nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (a - 1 / 3), sq_nonneg (a * (a - 1 / 2)), sq_nonneg ((1 - a) * ((1 - a) - 1 / 2)), mul_pos ha (show 0 < (1 - a) by nlinarith), mul_pos ha (show 0 < (1 - a) by nlinarith)]
      have pos5 : 0 < 3 * (a ^ 2 + b) * (a + b ^ 2) := by
        positivity
      apply div_nonpos_of_nonpos_of_nonneg h4 (by positivity)
    linarith
  · -- Second part: prove a/(a+b^3) + b/(a^3+b) ≤ 8/5
    have h1 : 0 < a * b := by
      nlinarith
    have h2 : a / (a + b ^ 3) + b / (a ^ 3 + b) - 8 / 5 ≤ 0 := by
      have pos1 : 0 < a + b ^ 3 := by
        nlinarith [sq_nonneg b, sq_nonneg (b ^ 2)]
      have pos2 : 0 < a ^ 3 + b := by
        nlinarith [sq_nonneg a, sq_nonneg (a ^ 2)]
      have pos3 : 0 < (a + b ^ 3) * (a ^ 3 + b) := by
        positivity
      have h3 : a / (a + b ^ 3) + b / (a ^ 3 + b) - 8 / 5 =
          (5 * a * (a ^ 3 + b) + 5 * b * (a + b ^ 3) - 8 * (a + b ^ 3) * (a ^ 3 + b)) / (5 * (a + b ^ 3) * (a ^ 3 + b)) := by
        field_simp
        <;> ring
      rw [h3] at *
      have h4 : 5 * a * (a ^ 3 + b) + 5 * b * (a + b ^ 3) - 8 * (a + b ^ 3) * (a ^ 3 + b) ≤ 0 := by
        rw [show b = 1 - a by linarith]
        nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (a - 1 / 2), sq_nonneg (a - 1 / 3), sq_nonneg (a * (a - 1 / 2)), sq_nonneg ((1 - a) * ((1 - a) - 1 / 2)), sq_nonneg ((a - 1 / 2) * (a - 1 / 2)), mul_pos ha (show 0 < (1 - a) by nlinarith), mul_pos ha (show 0 < (1 - a) by nlinarith), sq_nonneg (a * (1 - a)), sq_nonneg ((1 - a) ^ 2 - a ^ 2)]
      have pos5 : 0 < 5 * (a + b ^ 3) * (a ^ 3 + b) := by
        positivity
      apply div_nonpos_of_nonpos_of_nonneg h4 (by positivity)
    linarith