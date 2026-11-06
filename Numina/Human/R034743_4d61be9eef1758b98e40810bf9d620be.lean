import Mathlib

/- Let $a,b,c,d$ be positive reals such taht $a+b+c+d=1$.

Prove that: \[6(a^{3}+b^{3}+c^{3}+d^{3})\geq a^{2}+b^{2}+c^{2}+d^{2}+\frac{1}{8}.\] -/
theorem inequalities_27857 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = 1) :
    6 * (a^3 + b^3 + c^3 + d^3) ≥ a^2 + b^2 + c^2 + d^2 + 1 / 8 := by 
  nlinarith [sq_nonneg (a + b + c + d), sq_nonneg (a - 1 / 4), sq_nonneg (b - 1 / 4), sq_nonneg (c - 1 / 4), sq_nonneg (d - 1 / 4)]