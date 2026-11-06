import Mathlib

/- A map of the town that Annie and Barbara live in can be represented by the Cartesian plane. Annie is located at $(3,5)$ and Barbara says she is located at $(-6,2)$. They agree to meet the midpoint of their current locations. However, it turns out that Barbara read the map wrong, and she is actually at $(-10,4)$. What is the positive difference in the $x$-coordinates of where they agreed to meet and where they should actually meet? -/
theorem algebra_21938 (x1 x2 : ℝ) (y1 y2 : ℝ)
    (h1 : x1 = 3) (h2 : y1 = 5) (h3 : x2 = -6) (h4 : y2 = 2)
    (h5 : x3 = -10) (h6 : y3 = 4) :
    |(x1 + x2) / 2 - (x1 + x3) / 2| = 2 := by
  -- since the problem only asks for difference in x-coordinates, we can ignore y-parts.
  -- they agreed to meet is (x1+x2)/2 = (3+(-6))/2 = -3/2
  -- they should actually meet is (x1+x3)/2 = (3+(-10))/2 = -7/2
  -- positive difference is -3/2 - -7/2 = 2
  rw [h1, h3, h5]; norm_num