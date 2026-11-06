import Mathlib

/- A large urn contains 100 balls, of which 36% are red and the rest are blue. How many of the blue balls must be removed so that the percentage of red balls in the urn will be 
72%? (No red balls are to be removed.)
(A) 28(B) 32(C) 36(D) 50(E) 64 -/
theorem algebra_97876 {x red blue: ℕ} (hred: red = (0.36:ℝ)*100) (htot: 100 = red + blue) (h: blue - x = (0.72:ℝ) * (red + blue - x))  :
x = 50 := by 
--find how many blue balls are in the urn
    rify at htot
    rw[hred] at htot
    ring_nf at htot
    have hblue := congrFun (congrArg HAdd.hAdd htot) (-36)
--substitute in the equation involving x, and solve with linear algebra for x
    ring_nf at hblue
    rw[← hblue, hred] at h
    ring_nf at h
    linarith