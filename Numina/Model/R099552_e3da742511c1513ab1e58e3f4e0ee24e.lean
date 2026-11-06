import Mathlib

theorem inequalities_65124 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 2 * b * (b - c) / (a + b) + b ^ 2 * c * (c - a) / (b + c) +
    c ^ 2 * a * (a - b) / (c + a) ≥ 0 := by
  have pos1 : 0 < a + b := by positivity
  have pos2 : 0 < b + c := by positivity
  have pos3 : 0 < c + a := by positivity
  have eq1 : a ^ 2 * b * (b - c) / (a + b) + b ^ 2 * c * (c - a) / (b + c) +
      c ^ 2 * a * (a - b) / (c + a) ≥ 0 := by 
    have h1 : a ^ 2 * b * (b - c) / (a + b) + b ^ 2 * c * (c - a) / (b + c) +
        c ^ 2 * a * (a - b) / (c + a) = (a ^ 2 * b * (b - c) * (b + c) * (c + a) + b ^ 2 * c * (c - a) * (a + b) * (c + a) + c ^ 2 * a * (a - b) * (a + b) * (b + c)) / ((a + b) * (b + c) * (c + a)) := by 
      field_simp
      <;> ring
    rw [h1]
    apply div_nonneg 
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, mul_nonneg (show 0 ≤ a * b by positivity) (show 0 ≤ b * c by positivity), mul_nonneg (show 0 ≤ b * c by positivity) (show 0 ≤ c * a by positivity), mul_nonneg (show 0 ≤ c * a by positivity) (show 0 ≤ a * b by positivity)]
    positivity
  linarith