import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_296589 (a b c d : ℝ) (ha : 0 < a) (hd : 0 < d)
  (hdc : d ≤ c) (hcb : c ≤ b) (hba : b ≤ a) :
  (1 + c / (a + b)) * (1 + d / (b + c)) * (1 + a / (c + d)) * (1 + b / (d + a)) ≥
  (3 / 2) ^ 4 := by
  have h1 : 0 < a + b := by
    linarith
  have h2 : 0 < b + c := by
    linarith
  have h3 : 0 < c + d := by
    linarith
  have h4 : 0 < d + a := by
    linarith
  have h5 : (1 + c / (a + b)) * (1 + d / (b + c)) * (1 + a / (c + d)) * (1 + b / (d + a)) =
      ((a + b + c) * (b + c + d) * (a + c + d) * (a + b + d)) / ((a + b) * (b + c) * (c + d) * (d + a)) := by
    field_simp
    <;> ring
  rw [h5]
  have h6 : 0 < (a + b) * (b + c) * (c + d) * (d + a) := by
    positivity
  suffices ((a + b + c) * (b + c + d) * (a + c + d) * (a + b + d)) ≥ (3 / 2) ^ 4 * ((a + b) * (b + c) * (c + d) * (d + a)) by
    have h7 : ((a + b + c) * (b + c + d) * (a + c + d) * (a + b + d)) / ((a + b) * (b + c) * (c + d) * (d + a)) ≥ (3 / 2) ^ 4 := by
      apply (le_div_iff₀ h6).mpr
      linarith
    linarith
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - d),
    sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - d),
    sq_nonneg (a + b - c - d), sq_nonneg (b + c - d - a),
    sq_nonneg (a + d - b - c), sq_nonneg (b + a - c - d),
    mul_pos ha (show 0 < b by linarith),
    mul_pos (show 0 < b by linarith) (show 0 < c by linarith),
    mul_pos (show 0 < c by linarith) hd, 
    mul_pos ha hd, 
    mul_nonneg (show 0 ≤ a - b by linarith) (show 0 ≤ b - c by linarith), 
    mul_nonneg (show 0 ≤ b - c by linarith) (show 0 ≤ c - d by linarith), 
    mul_nonneg (show 0 ≤ a - b by linarith) (show 0 ≤ c - d by linarith)
    ]