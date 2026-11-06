import Mathlib

/- Let $a, b$ and $c$ be positive real numbers such that $a+b+c = abc$. Prove that at least one of $a, b$ or $c$ is greater than $\frac{17}{10}$ . -/
theorem inequalities_63247 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = a * b * c) :
    17 / 10 < a ∨ 17 / 10 < b ∨ 17 / 10 < c := by 
  by_contra!
  nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, h]