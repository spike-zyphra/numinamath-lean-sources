import Mathlib

theorem algebra_163200 (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0)
    (h1 : x + y + z = 50) (h2 : 20 * (1 / 2 * x + 1 / 3 * y + 1 / 4 * z) = 20) :
    0.6 * x + 0.5 * y + 0.3 * z = 270000 := by
  have h3 : 1 / 2 * x + 1 / 3 * y + 1 / 4 * z = 1 := by 
    linarith 
  have eq3 : 6 * x + 4 * y + 3 * z = 12 := by
    linarith
  -- Then from h1: x + y + z = 50, multiply by 3: 3x + 3y + 3z = 150
  have mul_eq1 : 3 * x + 3 * y + 3 * z = 150 := by
    linarith [h1]
  -- Subtracting equations
  -- 6x + 4y + 3z = 12 
  -- 3x + 3y + 3z = 150
  -- Subtract: 3x + y = -138
  have mul_eq2 : 3 * x + y = -138 := by 
    linarith [eq3, mul_eq1]
  -- Using variable bounds. From mul_eq2 (x, y >= 0) contradiction:
  -- x >= 0 -> 3 * x >= 0
  -- y >= 0
  -- Therefore, 3 * x + y >= 0
  -- But here 3 * x + y = -138 < 0. Contradiction.
  linarith [hx, hy, mul_eq2]