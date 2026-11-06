import Mathlib

open Real

theorem inequalities_7332 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (c ^ 2 * (c ^ 2 + a ^ 2)) / (b * a ^ 2) + (a ^ 2 * (a ^ 2 + b ^ 2)) / (c * b ^ 2) +
    (b ^ 2 * (b ^ 2 + c ^ 2)) / (a * c ^ 2) ≥ 2 * a + 2 * b + 2 * c := by 
  have h1 : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
  have h2 : 0 < a * b := mul_pos ha hb
  have h3 : 0 < b * c := mul_pos hb hc
  have h4 : 0 < a * c := mul_pos ha hc

  have h_pos1 : 0 < b * a ^2 := by positivity
  have h_pos2 : 0 < c * b ^2 := by positivity
  have h_pos3 : 0 < a * c ^2 := by positivity
  
  have h5 : (c ^ 2 * (c ^ 2 + a ^ 2)) / (b * a ^ 2) + (a ^ 2 * (a ^ 2 + b ^ 2)) / (c * b ^ 2) +
  (b ^ 2 * (b ^ 2 + c ^ 2)) / (a * c ^ 2) - 2 * a - 2 * b - 2 * c ≥ 0 := by 
    have h5' : (c ^ 2 * (c ^ 2 + a ^ 2)) / (b * a ^ 2) + (a ^ 2 * (a ^ 2 + b ^ 2)) / (c * b ^ 2) +
      (b ^ 2 * (b ^ 2 + c ^ 2)) / (a * c ^ 2) - 2 * a - 2 * b - 2 * c =
      ((c ^ 2 * (c^2 + a^2) * (c * b^2) * (a * c^2)) + (a^2 * (a^2 + b^2) * (b * a^2) * (a * c^2)) + (b^2 * (b^2 + c^2) * (b * a^2) * (c * b^2)) - 2 * a * (b * a^2) * (c * b^2) * (a * c^2) - 2 * b * (b * a^2) * (c * b^2) * (a * c^2) - 2 * c * (b * a^2) * (c * b^2) * (a * c^2)) / ((b * a^2) * (c * b^2) * (a * c^2)) := by
      field_simp
      <;> ring
    rw [h5']
    have h6 : (b * a^2) * (c * b^2) * (a * c^2) > 0 := by positivity
    have h7 : (c ^ 2 * (c^2 + a^2) * (c * b^2) * (a * c^2) + a^2 * (a^2 + b^2) * (b * a^2) * (a * c^2) + b^2 * (b^2 + c^2) * (b * a^2) * (c * b^2) - 2 * a * (b * a^2) * (c * b^2) * (a * c^2) - 2 * b * (b * a^2) * (c * b^2) * (a * c^2) - 2 * c * (b * a^2) * (c * b^2) * (a * c^2)) ≥ 0 := by
      nlinarith [sq_nonneg (a * b * c - b * c^2), sq_nonneg (a * b * c - a^2 * b), sq_nonneg (a * b * c - b * c * a), sq_nonneg (a^2 * b * c - b^2 * c * a), sq_nonneg (b^2 * c * a - b * c^2 * a), sq_nonneg (c^2 * a * b - a^2 * b * c), sq_nonneg (a ^2 - b^2), sq_nonneg (b ^2 - c^2), sq_nonneg (c ^2 - a^2), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), sq_nonneg (a^2 * (a - b)), sq_nonneg (a^2 * (a - c)), sq_nonneg (b^2 * (b - a)), sq_nonneg (b^2 * (b - c)), sq_nonneg (c^2 * (c - a)), sq_nonneg (c^2 * (c - b)), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos (show 0 < a * b from by positivity) (show 0 < a * c from by positivity), mul_pos (show 0 < a * b from by positivity) (show 0 < b * c from by positivity), mul_pos (show 0 < a * c from by positivity) (show 0 < b * c from by positivity)]
    apply div_nonneg
    linarith
    all_goals positivity
  linarith
  all_goals positivity