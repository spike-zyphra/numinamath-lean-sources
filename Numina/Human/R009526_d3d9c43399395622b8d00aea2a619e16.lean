import Mathlib

/- The mean, median, and mode of the 7 data values 60,100,x,40,50,200,90 are all equal to x.
What is the value of x?
(A) 50(B) 60(C) 75(D) 90(E) 100 -/
theorem algebra_95796 (x : ℝ) (h : x ≠ 0) (h1 : (60 + 100 + x + 40 + 50 + 200 + 90) / 7 = x)
(h2 : (60 + 100 + x + 40 + 50 + 200 + 90) / 7 = (x + 40) / 2) (h3 : (60 + 100 + x + 40 + 50 + 200 + 90) / 7 = x) :
x = 90 := by linarith
-- get x out of the equation of the mean h1, using linear arithmetic