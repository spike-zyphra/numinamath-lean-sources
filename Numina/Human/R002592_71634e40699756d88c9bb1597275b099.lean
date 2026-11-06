import Mathlib

/- On a certain math exam, 10% of the students got 70 points, 25% got 80 points, 20% got 85 points, 15% got 90 points, and the rest got 95 points.  
What is the difference between the mean and the median score on this exam?
(A)  0(B)  1(C)  2(D)  4(E)  5 -/
theorem algebra_95915 (a b c d e : ℝ)
(ha : a = 0.1) (hb : b = 0.25) (hc : c = 0.2) (hd : d = 0.15)
(he : e = 0.3) :
(70 * a + 80 * b + 85 * c + 90 * d + 95 * e) -
(85) = 1 := by
-- its an equation and it suffices to substitute the value of a b c d e
rw [ha, hb, hc, hd, he]
-- and then do the calculation
ring