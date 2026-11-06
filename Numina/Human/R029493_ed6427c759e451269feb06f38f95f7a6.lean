import Mathlib

/- Let $a,b \in R^+$ with $ab = 1$, prove that
$$\frac{1}{a^3 + 3b}+\frac{1}{b^3 + 3a}\le  \frac12.$$ -/
theorem inequalities_80941 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a * b = 1) :
    1 / (a ^ 3 + 3 * b) + 1 / (b ^ 3 + 3 * a) ≤ 1 / 2 := by 
  have ha' : 0 < a ^ 3 + 3 * b := by positivity
  have hb' : 0 < b ^ 3 + 3 * a := by positivity
  field_simp [ha.ne', hb.ne', ha'.ne', hb'.ne']
  rw [div_le_div_iff (by positivity) (by positivity)]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - 1),
    sq_nonneg (b - 1), hab, mul_self_nonneg (a * b - 1)]