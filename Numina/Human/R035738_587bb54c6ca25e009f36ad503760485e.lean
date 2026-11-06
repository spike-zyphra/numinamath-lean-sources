import Mathlib
open Real

/- Let $a,b,c \in \mathbb{R}^{+}$ such that $abc=1$. Prove that:

$$a^2b + b^2c + c^2a \ge \sqrt{(a+b+c)(ab + bc +ca)}$$-/

theorem inequalities_27064 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) :
    a ^ 2 * b + b ^ 2 * c + c ^ 2 * a ≥ sqrt ((a + b + c) * (a * b + b * c + c * a)) := by
  rw [ge_iff_le, Real.sqrt_le_iff]
  constructor
  . -- First show that 0 ≤ a²b + b²c + c²a.
    positivity
  . -- Then show that (a²b + b²c + c²a)² ≥ (a + b + c)(ab + bc + ca), which can be solved by combining (ab - bc)² ≥ 0, (bc - ca)² ≥ 0, (ca - ab)² ≥ 0 and a, b, c > 0.
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]