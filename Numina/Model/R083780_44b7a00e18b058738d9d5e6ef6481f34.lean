import Mathlib

theorem algebra_18917 (k : ℝ → ℝ) (hk : k = fun y => 1 / (2 * y + 1)) :
    {y | y ≠ -1 / 2} = {y | y < -1 / 2 ∨ y > -1 / 2} := by 
  ext y
  simp
  <;> omega