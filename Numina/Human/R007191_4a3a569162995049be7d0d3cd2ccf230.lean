import Mathlib

/-There are 3 complex numbers $a+bi$, $c+di$, and $e+fi$. If $b=1$, $e=-a-c$, and the sum of the numbers is $-i$, find $d+f$.-/
theorem algebra_12186 {a b c d e f : ℝ} (hb : b = 1) (he : e = -a - c) (hsum : a + b * Complex.I + (c + d * Complex.I) + (e + f * Complex.I) = - Complex.I) :
    d + f = -2 := by
  -- convert hsum to two equations
  -- show that a + c + e = 0
  have eq₁ : ((a + c + e) + (b + d + f) * Complex.I).re = (-Complex.I).re := by
    congr
    ring_nf at hsum ⊢
    exact hsum
  norm_num at eq₁
  rw [he] at eq₁
  -- show that b + d + f = -1
  have eq₂ : ((a + c + e) + (b + d + f) * Complex.I).im = (-Complex.I).im := by
    congr
    ring_nf at hsum ⊢
    exact hsum
  norm_num at eq₂
  -- calculation
  calc
    d + f = (b + d + f) - b := by ring_nf
    _ = -1 - 1 := by rw [eq₂, hb]
    _ = -2 := by norm_num