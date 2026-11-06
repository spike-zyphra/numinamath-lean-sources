import Mathlib

/- Orvin went to the store with just enough money to buy 30 balloons. 
When he arrived he discovered that the store had a special sale on balloons: buy 1 balloon at the regular price and get a second at 1/3 ​off the regular price. 
What is the greatest number of balloons Orvin could buy?
(A) 33(B) 34(C) 36(D) 38(E) 39 -/
theorem algebra_96304 (x y : ℝ) (hx : x > 0) (h : y = (30 * x) / (1 * x + (1 - 1 / 3) * x)) :
2 * y = 36 := by
-- use the hypotheses h to derive how many sets of 2 baloons one buys, notice that x cancels out and one has 18 pairs!
  rw [h]
  ring_nf
  field_simp