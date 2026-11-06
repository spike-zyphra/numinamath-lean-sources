import Mathlib

/- Prove that for any three positive real numbers $ a,b,c, \frac{1}{a\plus{}b}\plus{}\frac{1}{b\plus{}c}\plus{}\frac{1}{c\plus{}a} \ge \frac{9}{2} \cdot \frac{1}{a\plus{}b\plus{}c}$. -/
theorem inequalities_60401 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    9 / 2 * 1 / (a + b + c) ≤ 1 / (a + b) + 1 / (b + c) + 1 / (c + a) := by 
  field_simp
  rw [div_le_div_iff (by positivity) (by positivity)]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]