import Mathlib

/- Prover que pour tous réels strictement positifs $a, b, c$ tels que $a b c=1$, on a

$$
\frac{1}{1+a^{2}+(b+1)^{2}}+\frac{1}{1+b^{2}+(c+1)^{2}}+\frac{1}{1+c^{2}+(a+1)^{2}} \leqslant \frac{1}{2}
$$ -/
theorem inequalities_604420 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 / (1 + a ^ 2 + (b + 1) ^ 2) +
    1 / (1 + b ^ 2 + (c + 1) ^ 2) +
    1 / (1 + c ^ 2 + (a + 1) ^ 2) ≤ 1 / 2 := by
  have h₁ : 1 / (1 + a ^ 2 + (b + 1) ^ 2) ≤ 1 / (2 * (1 + a * b + b)) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith [sq_nonneg (a - b)]
  have h₂ : 1 / (1 + b ^ 2 + (c + 1) ^ 2) ≤ 1 / (2 * (1 + b * c + c)) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith [sq_nonneg (b - c)]
  have h₃ : 1 / (1 + c ^ 2 + (a + 1) ^ 2) ≤ 1 / (2 * (1 + c * a + a)) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith [sq_nonneg (c - a)]
  have h₄ : 1 / (2 * (1 + a * b + b)) + 1 / (2 * (1 + b * c + c)) + 1 / (2 * (1 + c * a + a)) = 1 / 2 := by
    field_simp [show a * b * c = 1 by linarith]
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), habc, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  linarith [h₁, h₂, h₃, h₄]