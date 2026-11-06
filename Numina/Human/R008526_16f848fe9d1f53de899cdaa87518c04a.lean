import Mathlib

/- The length of a rectangle is $3x+10$ feet and its width is $x+12$ feet.  If the perimeter of the rectangle is 76 feet, how many square feet are in the area of the rectangle? -/
theorem algebra_19701 {x : ℝ} (hx : x > 0) (h : 2 * (3 * x + 10 + x + 12) = 76) :
    (3 * x + 10) * (x + 12) = 352 := by 
  nlinarith