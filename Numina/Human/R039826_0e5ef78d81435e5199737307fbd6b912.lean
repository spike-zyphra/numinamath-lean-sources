import Mathlib

open Polynomial

/- What is the degree of the polynomial $(x^4+ax^7+bx+c)(x^3+dx^2+e)(x+f)$, where letters $a$ through $f$ are all nonzero constants? -/
theorem algebra_17231 {a b c d e f : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (he : e ≠ 0) (hf : f ≠ 0) :
    ((X ^ 4 + C a * X ^ 7 + C b * X + C c) * (X ^ 3 + C d * X ^ 2 + C e) * (X + C f)).degree = 11 := by compute_degree!
