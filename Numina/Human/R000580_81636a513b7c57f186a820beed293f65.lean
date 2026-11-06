import Mathlib

/- An equilateral triangle has sides of length 2 units. A second equilateral triangle is formed having sides that are $150\%$ of the length of the sides of the first triangle. A third equilateral triangle is formed having sides that are $150\%$ of the length of the sides of the second triangle. The process is continued until four equilateral triangles exist. What will be the percent increase in the perimeter from the first triangle to the fourth triangle? Express your answer to the nearest tenth. -/
theorem algebra_12884 (a b c d : ℝ) (ha : a = 2) (hb : b = 150 / 100 * a) (hc : c = 150 / 100 * b) (hd : d = 150 / 100 * c) :
    round ((3 * d - 3 * a) / (3 * a) * 1000) / (10 : ℝ) = 237.5 := by
  simp_all
  ring_nf
  norm_num