import Mathlib

/- The sum of two positive numbers is 5 times their difference. What is the ratio of the larger number to the smaller number?
(A) 5/4
(B) 3/2
(C) 9/5
(D) 2
(E) 5/2
  -/
theorem algebra_95292 {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h : x + y = 5 * (x - y)) : max x y / min x y = 3 / 2 := by
  -- first simplify equation to get 3y = 2x, from this infer that x > y
  have h : 3 * y = 2 * x := by linarith
  have h': x > y := by linarith
  -- now establish that max(x, y) = x and min(x, y) = y
  have hx : max x y = x := by
    simp
    linarith
  have hy : min x y = y := by
    simp
    linarith
  -- change max, min expressions in target and then simplify to prove x / y = 3 / 2
  rw [hx, hy]
  field_simp
  linarith