import Mathlib

/- Given that $a$ and $b$ are positive integers and that $a+b=24$, what is the value of $ab$ if $2ab + 10a = 3b + 222$? -/
theorem algebra_13154 {a b : ℤ} (ha : 0 < a) (hb : 0 < b)
    (h1 : a + b = 24) (h2 : 2 * a * b + 10 * a = 3 * b + 222) :
    a * b = 108 := by
  nlinarith