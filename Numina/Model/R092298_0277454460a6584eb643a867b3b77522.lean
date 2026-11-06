import Mathlib

theorem inequalities_598935 (a b : ℝ) (ha : 1 < a) (hb : 1 < b) :
    a ^ 2 / (b - 1) + b ^ 2 / (a - 1) ≥ 8 := by
  have h1 : 0 < b - 1 := by linarith
  have h2 : 0 < a - 1 := by linarith
  have h3 : a ^ 2 / (b - 1) + b ^ 2 / (a - 1) - 8 ≥ 0 := by 
    have pos1 : 0 < (b - 1) * (a - 1) := mul_pos (by linarith) (by linarith)
    have h4 : a ^ 2 / (b - 1) + b ^ 2 / (a - 1) - 8 = (a ^ 2 * (a - 1) + b ^ 2 * (b - 1) - 8 * (b - 1) * (a - 1)) / ((b - 1) * (a - 1)) := by 
      field_simp
      <;> ring
    rw [h4]
    have h5 : a ^ 2 * (a - 1) + b ^ 2 * (b - 1) - 8 * (b - 1) * (a - 1) ≥ 0 := by 
      nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (a - b), sq_nonneg (a * (a - 2)), sq_nonneg (b * (b - 2)), sq_nonneg ((a - 2) * (b - 2)), sq_nonneg (a * (b - a)), sq_nonneg (b * (a - b)), mul_nonneg (by linarith : 0 ≤ a - 1) (by linarith : 0 ≤ b - 1)]
    apply div_nonneg h5 (by positivity)
    all_goals try positivity
  linarith