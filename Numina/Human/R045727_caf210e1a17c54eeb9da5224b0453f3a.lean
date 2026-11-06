import Mathlib
open Real

/- If x/y=3/4, then the incorrect expression in the following is:
(A) （x+y）/y=7/4 (B) y/(y-x)=4/1 (C) (x+2y)/x=11/3 (D) x/2y=3/8 (E) (x-y)/y=1/4 -/
theorem algebra_94246 {x y : ℝ} (hy : y ≠ 0) (h : x / y = 3 / 4) :
(x - y) / y ≠ 1 / 4 := by
  -- prove by contradiction
  intro hx
  -- we first simplify hx into an expression about x/y
  have h2 : (x - y) / y = x / y - 1 := by field_simp [hy]
  rw [h2] at hx
  -- then we substitute the value of x/y into hx,
  rw [h] at hx
  -- showing they're not the same
  linarith