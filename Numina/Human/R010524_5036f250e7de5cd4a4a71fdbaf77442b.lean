import Mathlib

/- At each basketball practice last week, Jenny made twice as many free throws as she made at the previous practice. 
At her fifth practice she made 48 free throws. How many free throws did she make at the first practice?
(A) 3(B) 6(C) 9(D) 12(E) 15 -/
theorem algebra_95486 (x : ℕ) (hx : x ≠ 0) (h : x * 2^4 = 48) :
x = 3 := by
--h tells one has to divide 48 in half for four times to know the free throws of the first practice, then rewrite and solve the equation.
norm_num at h
omega