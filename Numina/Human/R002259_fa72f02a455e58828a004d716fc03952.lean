import Mathlib

/- Let $a,b,c$ and $d$ be positive real numbers such that $a^2+b^2+c^2+d^2 \ge 4$. Prove that
$$(a+b)^3+(c+d)^3+2(a^2+b^2+c^2+d^2) \ge 4(ab+bc+cd+da+ac+bd)$$ -/
theorem inequalities_78038 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a^2 + b^2 + c^2 + d^2 ≥ 4) :
    (a + b)^3 + (c + d)^3 + 2 * (a^2 + b^2 + c^2 + d^2) ≥
    4 * (a * b + b * c + c * d + d * a + a * c + b * d) := by 
  nlinarith [sq_nonneg (a + b - 2), sq_nonneg (c + d - 2),
    sq_nonneg (a - b), sq_nonneg (c - d),
    sq_nonneg (a + b - c - d), sq_nonneg (a - b - c + d)]