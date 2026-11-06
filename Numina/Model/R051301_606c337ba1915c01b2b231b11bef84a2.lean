import Mathlib

theorem algebra_162878 (a b c d : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hord : a > b ∧ b > c ∧ c > d) (hsum : a + b + c + d = 2004)
    (hdiff : a^2 - b^2 + c^2 - d^2 = 2004) :
    a ≥ 503 := by
  have h1 : a > b := hord.left
  have h2 : b > c := hord.right.left
  have h3 : c > d := hord.right.right
  nlinarith [sq_nonneg (a - 503), sq_nonneg (b - 501), sq_nonneg (c - 500), sq_nonneg (d - 499),
          hsum, hdiff, h1, h2, h3, sq_nonneg (a - c), sq_nonneg (b - d)]