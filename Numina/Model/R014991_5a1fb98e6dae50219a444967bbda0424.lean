import Mathlib

open Real

theorem algebra_278302 {a k : ℝ} {P : ℝ} (ha : 0 < a ∧ a ≠ 1) (hk : 0 < k) (hP : 0 < P) :
    logb (a ^ k) P = logb a P / k := by
  have h1 : logb (a ^ k) P = log P / log (a ^ k) := by
    field_simp [logb]
  have h2 : logb a P = log P / log a := by
    field_simp [logb]
  have h3 : log (a ^ k) = k * log a := by 
    rw [log_rpow]
    all_goals linarith
  rw [h1]
  rw [h2]
  rw [h3]
  <;> field_simp
  <;> ring