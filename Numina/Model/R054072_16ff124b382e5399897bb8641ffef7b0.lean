import Mathlib

/- Positive integers $a$, $b$, $c$, $d$ satisfy $\frac{2}{3}<{}\frac{a}{b}<{}\frac{c}{d}<{}\frac{3}{4}$, when $a+b+c+d$ is minimized, $c=$ ___          ___ , $d=$ ___          ___. -/
theorem number_theory_376 (a b c d : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : 2 / 3 < a / b ∧ a / b < c / d ∧ c / d < 3 / 4) :
    a + b + c + d = 18 ∧ c = 5 ∧ d = 7 := by
  omega