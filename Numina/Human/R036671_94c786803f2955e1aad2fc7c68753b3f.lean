import Mathlib

theorem algebra_202537 {x y z : ℝ} (h1 : 5732 * x + 2134 * y + 2134 * z = 7866)
    (h2 : 2134 * x + 5732 * y + 2134 * z = 670) (h3 : 2134 * x + 2134 * y + 5732 * z = 11464) :
    (x, y, z) = (1, -1, 2) := by
  have hx : x = 1 := by 
    linarith [h1, h2, h3]
  have hy : y = -1 := by 
    linarith [h1, h2, h3]
  have hz : z = 2 := by 
    linarith [h1, h2, h3]
  exact Prod.ext hx (Prod.ext hy hz)