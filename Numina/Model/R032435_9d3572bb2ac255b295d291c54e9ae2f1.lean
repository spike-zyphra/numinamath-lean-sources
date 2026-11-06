import Mathlib

open Real

theorem algebra_95765 {rem : ℝ → ℝ → ℝ} (hrem : ∀ x y, y ≠ 0 → rem x y = x - y * ⌊x / y⌋) :
rem (3 / 8) (-2 / 5) = -1 / 40 := by
  have h1 : rem (3 / 8 : ℝ) (-2 / 5 : ℝ) = (3 / 8 : ℝ) - (-2 / 5 : ℝ) * ⌊(3 / 8 : ℝ) / (-2 / 5 : ℝ)⌋ := by
    apply hrem
    norm_num
  rw [h1]
  have h2 : ⌊(3 / 8 : ℝ) / (-2 / 5 : ℝ)⌋ = -1 := by
    norm_num [Int.floor_eq_iff]
  rw [h2]
  norm_num