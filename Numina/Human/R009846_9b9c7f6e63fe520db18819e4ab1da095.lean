import Mathlib

/- A 40-foot by 10-foot rectangular garden is enclosed by a fence. To make the garden larger, while using the same amount of fencing, its shape is changed to a square. How many square feet larger than the old garden is the new garden? -/
theorem algebra_16456 (x : ℝ) (hx : x > 0) (h : 2 * (40 + 10) = 4 * x) :
    x ^ 2 - (40 * 10) = 225 := by
  nlinarith