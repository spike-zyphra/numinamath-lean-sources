import Mathlib

/- Halfway through a 100-shot archery tournament, Chelsea leads by 50 points. For each shot a bullseye scores 10 points, with other possible scores being 8, 4, 2, and 0 points. Chelsea always scores at least 4 points on each shot. 
If Chelsea's next n shots are bullseyes she will be guaranteed victory. 
What is the minimum value for n?
(A) 38
(B) 40
(C) 42
(D) 44
(E) 46 -/
theorem algebra_94140 (n k : ℤ) (h : k + n * 10 + 4 * (50 - n) > (k - 50) + 50 * 10) 
: n ≥ 42 := by
  --solve the inequality at h by linear arithmetic and conclude
  linarith