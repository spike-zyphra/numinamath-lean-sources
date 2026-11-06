import Mathlib

/- There are 3 complex numbers $a+bi$, $c+di$, and $e+fi$. If $b=3$, $e=-a-c$, and the sum of the numbers is $2i$, find $d+f$. -/
theorem algebra_10946 (a b c d e f : ℝ) (ha : b = 3) (he : e = -a - c)
    (hsum : (a + b * Complex.I) + (c + d * Complex.I) + (e + f * Complex.I) = 2 * Complex.I) :
    d + f = -1 := by 
  simp_all [Complex.ext_iff]
  linarith