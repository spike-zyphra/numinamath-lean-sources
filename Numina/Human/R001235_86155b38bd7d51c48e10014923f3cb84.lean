import Mathlib

/-The number 4 is written on my whiteboard. Every time it rains, I multiply the number on the whiteboard by $\frac{2}{3}$, erase the original number, and write the new number on the whiteboard. When it snows, I multiply the number on the whiteboard by $\frac{3}{5}$, and I replace the original number with the new number. It has rained 5 times and snowed 4 times this month. At the end of the month, what number is on the whiteboard?-/
theorem algebra_21833 (origin : ℝ) (h1 : origin = 4) (h2 : rain = 5) (h3 : snow = 4) :
    4 * (2 / 3)^rain * (3 / 5)^snow = 128 / 1875 := by simp [h1, h2, h3]