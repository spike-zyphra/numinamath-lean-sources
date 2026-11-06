import Mathlib

/- A 5-inch by 7-inch picture is placed on a rectangular piece of red paper such that a 0.5-inch wide red border is seen along each side of the picture. What is the area of the visible red border, in square inches? -/
theorem algebra_21905 (a b : ℝ) (ha : a = 5) (hb : b = 7) :
    (a + 2 * 0.5) * (b + 2 * 0.5) - a * b = 13 := by 
  rw [ha, hb]; ring