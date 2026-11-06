import Mathlib

/- Find one solution in positive integers to the equation

$$
x^{2}-2 x-2007 y^{2}=0
$$ -/
theorem algebra_607994 (x y : ℤ) : (x, y) = (225, 5) → x > 0 ∧ y > 0 ∧ x ^ 2 - 2 * x - 2007 * y ^ 2 = 0 := by
  -- Verify that the pair (225, 5) is a solution.
  intro hxy
  simp at hxy
  rw [hxy.1, hxy.2]
  simp