import Mathlib

/- You have a square that has a side length of $1$ centimeter. Each minute, $2$ centimeters are added to the side length. After $10$ minutes, what will be the difference between the area of the last square and the area of the initial square in square centimeters (do not include the units in your answer)? -/
theorem algebra_20348 (side_length : ℝ) (h : side_length = 1) :
    (side_length + 2 * 10) ^ 2 - side_length ^ 2 = 440 := by
        rw [h]
        norm_num
