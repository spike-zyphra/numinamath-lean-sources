import Mathlib

open Real

theorem algebra_605332 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 1) :
  (a - b * c) / (a + b * c) + (b - c * a) / (b + c * a) + (c - a * b) / (c + a * b) ≤ 3 / 2 := by
  have g1 : 1 - a > 0:= by linarith
  have g2 : 1 - b > 0:= by linarith
  have g3 : 1 - c > 0:= by linarith
  have h1 : 1 - (a - b * c) / (a + b * c) = 2 * b * c / ((1 - b) * (1 - c)):= by
    replace h : a = 1 - b - c:= by linarith
    rw [h]
    rw [show 1 - b - c + b * c = (1 - b) * (1 - c) by ring]
    field_simp
    ring
  have h2 : 1 - (b - c * a) / (b + c * a) = 2 * c * a / ((1 - c) * (1 - a)):= by
    replace h : b = 1 - a - c:= by linarith
    rw [h]
    rw [show 1 - a - c + c * a = (1 - c) * (1 - a) by ring]
    field_simp
    ring
  have h3 : 1 - (c - a * b) / (c + a * b) = 2 * a * b / ((1 - a) * (1 - b)):= by
    replace h : c = 1 - a - b:= by linarith
    rw [h]
    rw [show 1 - a - b + a * b = (1 - a) * (1 - b) by ring]
    field_simp
    ring
  suffices 2 * a * b / ((1 - a) * (1 - b)) + 2 * b * c / ((1 - b) * (1 - c)) + 2 * c * a / ((1 - c) * (1 - a)) ≥ 3 / 2 by linarith
  have h' : 2 * a * b / ((1 - a) * (1 - b)) + 2 * b * c / ((1 - b) * (1 - c)) + 2 * c * a / ((1 - c) * (1 - a)) ≥ 3 / 2 := by
    have pos1 : (1 - a) * (1 - b) > 0 := by positivity
    have pos2 : (1 - b) * (1 - c) > 0 := by positivity
    have pos3 : (1 - c) * (1 - a) > 0 := by positivity
    have h'' : 2 * a * b / ((1 - a) * (1 - b)) + 2 * b * c / ((1 - b) * (1 - c)) + 2 * c * a / ((1 - c) * (1 - a)) - 3 / 2 ≥ 0 := by
      have h''': 2 * a * b / ((1 - a) * (1 - b)) + 2 * b * c / ((1 - b) * (1 - c)) + 2 * c * a / ((1 - c) * (1 - a)) - 3 / 2 =
          (4 * a * b * (1 - c) + 4 * b * c * (1 - a) + 4 * c * a * (1 - b) - 3 * ( (1 - a) * (1 - b) * (1 - c) )) / (2 * ( (1 - a) * (1 - b) * (1 - c) )) := by
        field_simp
        ring
      rw [h''']
      have pos4 : 2 * ( (1 - a) * (1 - b) * (1 - c) ) > 0 := by positivity
      have pos5 : 4 * a * b * (1 - c) + 4 * b * c * (1 - a) + 4 * c * a * (1 - b) - 3 * ( (1 - a) * (1 - b) * (1 - c) ) ≥ 0 := by
        have h4 : c = 1 - a - b := by linarith
        rw [h4]
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), 
          mul_pos ha hb, mul_pos ha (show 0 < 1 - a - b by nlinarith [h, ha, hb]), 
          mul_pos hb (show 0 < 1 - a - b by nlinarith [h, ha, hb]), 
          sq_nonneg (a * b - b * (1 - a - b)), sq_nonneg (b * (1 - a - b) - (1 - a - b) * a), sq_nonneg ( (1 - a - b) * a - a * b ) ]
      apply div_nonneg
      linarith
      all_goals positivity
    linarith
  linarith