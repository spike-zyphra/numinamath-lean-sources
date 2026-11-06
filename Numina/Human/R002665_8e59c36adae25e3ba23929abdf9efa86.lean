import Mathlib

def f (x y : ℝ) := 3 * x - y

/- Suppose that a∗b means 3a−b. What is the value of x if 2∗(5∗x)=1
(A) 1/10  (B) 2 (C) 10/3  (D) 10  (E) 14 -/

theorem algebra_98434 {x : ℝ} (hx : f 2 (f 5 x) = 1) : x = 10 := by 
 --write the definition of f in hx and then use arithmetic to conclude
  unfold f at hx
  linarith