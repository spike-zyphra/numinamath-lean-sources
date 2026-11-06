import Mathlib

/- Suppose that $a,b,$ and $c$ are positive integers satisfying $(a+b+c)^3 - a^3 - b^3 - c^3 = 150$. Find $a+b+c$. -/
theorem algebra_13839 {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : (a + b + c)^3 - a^3 - b^3 - c^3 = 150) : a + b + c = 6 := by
  ring_nf at h
  nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]