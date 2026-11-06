import Mathlib

theorem algebra_318092
    (a b c : ℤ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h1 : a * b + b * c + c * a + 2 * (a + b + c) = 8045)
    (h2 : a * b * c - a - b - c = -2) :
    a + b + c = 2012 := by

  have h_eq : a * b * c = a + b + c - 2 := by linarith

  have h3 : a + b + c = 2012 := by 
    nlinarith [sq_nonneg (a - b : ℤ), sq_nonneg (b - c : ℤ), sq_nonneg (c - a : ℤ), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
]

  exact h3