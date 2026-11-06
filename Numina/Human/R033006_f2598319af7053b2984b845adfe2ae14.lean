import Mathlib

open Polynomial

/- In the polynomial $(ax^6+bx^8+cx^3+d)(x^5+ex^4+f)(x^2+gx+h)$, letters $a$ through $h$ are all nonzero constants. What is the degree of the polynomial? -/
theorem algebra_21668 {a b c d e f g h : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (he : e ≠ 0) (hf : f ≠ 0) (hg : g ≠ 0) (hh : h ≠ 0) :
    ((C a * X ^ 6 + C b * X ^ 8 + C c * X ^ 3 + C d) * (X ^ 5 + C e * X ^ 4 + C f) * (X ^ 2 + C g * X + C h)).degree = 15 := by compute_degree!
