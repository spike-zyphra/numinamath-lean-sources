import Mathlib
/-Find the equation of line $l$ which passes through the intersection point of lines $x+y-2=0$ and $x-y+4=0$, and is parallel to line $3x-2y+4=0$.-/
theorem algebra_9365 {x y : ℝ} (h1 : x + y - 2 = 0) (h2 : x - y + 4 = 0)
    (h3 : 3 * x - 2 * y + 4 = 0) :
    3 * x - 2 * y + 9 = 0 := by linarith