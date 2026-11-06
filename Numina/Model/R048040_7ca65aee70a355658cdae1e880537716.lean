import Mathlib

theorem inequalities_598169 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h : a + b = 2) :
    2 ≤ a ^ 2 / (2 - a) + b ^ 2 / (2 - b) := by
  have h1 : b = 2 - a := by linarith
  have h2 : 2 - a > 0 := by
    nlinarith [h, ha, hb]
  have h3 : 2 - b > 0 := by
    nlinarith [h, ha, hb]
  
  rw [h1]
  have h4 : 2 - (2 - a) = a := by
    linarith

  rw [h4]

  have h7 : a ^ 2 / (2 - a) + (2 - a) ^ 2 / a - 2 ≥ 0 := by
    have h8 : a ^ 2 / (2 - a) + (2 - a) ^ 2 / a - 2 =
        (a ^ 3 + (2 - a) ^ 3 - 2 * a * (2 - a)) / (a * (2 - a)) := by
      field_simp [(show 2 - a ≠ 0 by linarith), (show a ≠ 0 by linarith)]
      ring
    rw [h8]
    have h8_pos : a ^ 3 + (2 - a) ^ 3 - 2 * a * (2 - a) ≥ 0 := by
      nlinarith [sq_nonneg (a - 1)]
    have pos1 : a * (2 - a) > 0 := by
      apply mul_pos
      linarith
      linarith
    apply div_nonneg
    linarith
    positivity

  linarith