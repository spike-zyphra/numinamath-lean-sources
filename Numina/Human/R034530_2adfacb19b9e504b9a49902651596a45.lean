import Mathlib

/- Let $a, b, c, x$ and $y$ be positive real numbers such that $ax + by \leq bx + cy \leq cx + ay$.

Prove that $b \leq c$. -/
theorem inequalities_25853 (a b c x y : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hx : 0 < x) (hy : 0 < y) (h1 : a * x + b * y ≤ b * x + c * y) (h2 : b * x + c * y ≤ c * x + a * y) :
    b ≤ c := by
  have hxy : 0 < x * y := mul_pos hx hy
  nlinarith [ha, hb, hc, h1, h2, mul_self_nonneg (x - y)]
  <;> linarith