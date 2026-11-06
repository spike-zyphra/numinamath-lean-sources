import Mathlib

theorem inequalities_44308 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a ^ 2 - b * c) / (2 * a ^ 2 + b * c) + (b ^ 2 - c * a) / (2 * b ^ 2 + c * a) +
    (c ^ 2 - a * b) / (2 * c ^ 2 + a * b) ≤ 0 := by
  have ha1 : 0 < a := ha
  have hb1 : 0 < b := hb
  have hc1 : 0 < c := hc
  
  have h1 : 0 < a * b := mul_pos ha1 hb1
  have h2 : 0 < a * c := mul_pos ha1 hc1
  have h3 : 0 < b * c := mul_pos hb1 hc1
  
  have h4 : 0 < 2 * a ^ 2 + b * c := by positivity
  have h5 : 0 < 2 * b ^ 2 + c * a := by positivity
  have h6 : 0 < 2 * c ^ 2 + a * b := by positivity
  
  have h7 : (a ^ 2 - b * c) / (2 * a ^ 2 + b * c) + (b ^ 2 - c * a) / (2 * b ^ 2 + c * a) + (c ^ 2 - a * b) / (2 * c ^ 2 + a * b) =
      ((a ^ 2 - b * c) * (2 * b ^ 2 + c * a) * (2 * c ^ 2 + a * b) +
       (b ^ 2 - c * a) * (2 * a ^ 2 + b * c) * (2 * c ^ 2 + a * b) +
       (c ^ 2 - a * b) * (2 * a ^ 2 + b * c) * (2 * b ^ 2 + c * a)) / ((2 * a ^ 2 + b * c) * (2 * b ^ 2 + c * a) * (2 * c ^ 2 + a * b)) := by
    field_simp
    <;> ring
  
  rw [h7]
  have h8 : 0 < (2 * a ^ 2 + b * c) * (2 * b ^ 2 + c * a) * (2 * c ^ 2 + a * b) := by positivity
  have h9 : (a ^ 2 - b * c) * (2 * b ^ 2 + c * a) * (2 * c ^ 2 + a * b) +
      (b ^ 2 - c * a) * (2 * a ^ 2 + b * c) * (2 * c ^ 2 + a * b) +
      (c ^ 2 - a * b) * (2 * a ^ 2 + b * c) * (2 * b ^ 2 + c * a) ≤ 0 := by
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
          sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)),
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          sq_nonneg (a * b + c * a - b * c), sq_nonneg (b * c + a * b - c * a), sq_nonneg (c * a + b * c - a * b),
          mul_pos ha1 hb1, mul_pos hb1 hc1, mul_pos ha1 hc1, mul_pos ha (show 0 < a from by linarith), mul_pos hb (show 0 < b from by linarith), mul_pos hc (show 0 < c from by linarith)]
  
  apply div_nonpos_of_nonpos_of_nonneg h9 (by positivity)