import Mathlib

/- 10. If $a+b+c=2 p$, then the following equality holds:


$$

(2 a p+b c)(2 b p+a c)(2 c p+a b)=(a+b)^{2}(a+c)^{2}(b+c)^{2}

$$


Prove. -/
theorem algebra_292383 [CommRing R] {a b c p : R} (h : a + b + c = 2 * p) :
    (2 * a * p + b * c) * (2 * b * p + a * c) * (2 * c * p + a * b) =
    (a + b)^2 * (a + c)^2 * (b + c)^2 := by
  -- Rewrite each 2 * a * p as 2 * p * a to prepare for substituting 2 * p with a + b + c
  trans (2 * p * a + b * c) * (2 * p * b + a * c) * (2 * p * c + a * b)
  · ring
  -- Substitute 2 * p with a + b + c using the hypothesis h, then simplify
  rw [←h]
  ring