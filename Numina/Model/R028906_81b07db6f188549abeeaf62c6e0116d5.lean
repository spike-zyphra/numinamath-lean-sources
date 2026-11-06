import Mathlib

theorem algebra_607994 (x y : ℤ) : (x, y) = (225, 5) → x > 0 ∧ y > 0 ∧ x ^ 2 - 2 * x - 2007 * y ^ 2 = 0 := by 
  intro h 
  rcases h with ⟨rfl, rfl⟩
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num