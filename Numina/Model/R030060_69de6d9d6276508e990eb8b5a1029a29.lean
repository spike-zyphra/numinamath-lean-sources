import Mathlib

open Real

theorem inequalities_66895 :
    (∀ x y z : ℝ, (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2)) ∧
    (∀ a b c : ℝ, a > 0 → b > 0 → c > 0 → a + b + c ≥ a * b * c → a ^ 2 + b ^ 2 + c ^ 2 ≥ sqrt 3 * a * b * c) := by
  constructor
  · -- Prove that $(x+y+z)^2 \le 3(x^2 +y^2 +z^2)$ for any real numbers $x,y,z$.
    intro x y z
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y + z - (x ^ 2 + y ^ 2 + z ^ 2)), sq_nonneg (x + y + z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
  · -- If positive numbers $a,b,c$ satisfy $a+b+c \ge abc$, prove that $a^2 +b^2 +c^2 \ge \sqrt3 abc$
    intro a b c ha hb hc habc
    have h1 : 0 < a * b * c := by
      apply mul_pos
      apply mul_pos
      all_goals linarith
    have h2 : 0 ≤ sqrt 3 := by
      apply Real.sqrt_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b + c - a * b * c), sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), habc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]