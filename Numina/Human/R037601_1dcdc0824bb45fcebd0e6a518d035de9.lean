import Mathlib

/- 6. Plot the graph of the equation $x^{2}-y^{4}=\sqrt{18 x-x^{2}-81}$, that is, represent on the coordinate plane all points with coordinates $(x ; y)$ that satisfy this equation. -/
theorem algebra_104225 (x y : ℝ) (hpos : 0 ≤ 18 * x - x^2 - 81) (hx : x^2 - y^4 = √(18 * x - x^2 - 81)) :
    (x, y) = (9, 3) ∨ (x, y) = (9, -3) := by
  -- factorise inside the square root
  rw [show 18 * x - x^2 - 81 = -(9 - x)^2 by ring] at hpos hx
  rw [←neg_nonpos, neg_neg] at hpos
  -- this implies the value for x
  have xval : x = 9 := by linarith [sq_eq_zero_iff.mp (le_antisymm hpos (by positivity))]
  -- substitute in for x
  simp [xval] at hx
  -- factorise the y term
  have hy : (3 - y) * (3 + y) * (9 + y^2) = 0 := by calc
    _ = 9^2 - y^4 := by ring
    _ = 0 := hx
  rcases mul_eq_zero.mp hy with hy' | hy'
  · rcases mul_eq_zero.mp hy' with hy'' | hy''
    · have yval : y = 3 := by linarith [hy'']
      left; exact Prod.ext xval yval
    · have yval : y = -3 := by linarith [hy'']
      right; exact Prod.ext xval yval
  -- the final term is positive
  have := calc
    -9 = y^2 := by linarith [hy']
     _ ≥ 0   := by positivity
  linarith