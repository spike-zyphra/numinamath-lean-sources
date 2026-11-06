import Mathlib

/- Let x=−2016. What is the value of 
|∣∣x∣−x∣−∣x∣|−x?
(A) −2016(B) 0(C) 2016(D) 4032(E) 6048 -/
theorem algebra_97379 (x : ℝ) (hx : x = -2016) : abs (abs (abs x - x) - abs x) - x = 4032 := by 
    --compute the claim by substituting the definition of abs and by using sums and subtractions
    rw[hx]
    simp
    ring_nf
    simp
    ring_nf
    simp
    ring_nf