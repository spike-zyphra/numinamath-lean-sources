import Mathlib

/- Prover que pour tous réels strictement positifs $a, b, c$ tels que $a b c=1$, on a

$$
\frac{1}{1+a^{2}+(b+1)^{2}}+\frac{1}{1+b^{2}+(c+1)^{2}}+\frac{1}{1+c^{2}+(a+1)^{2}} \leqslant \frac{1}{2}
$$ -/
/- Prouver que pour tous réels strictement positifs $a, b, c$ tels que $a b c=1$, on a

$$
\frac{1}{1+a^{2}+(b+1)^{2}}+\frac{1}{1+b^{2}+(c+1)^{2}}+\frac{1}{1+c^{2}+(a+1)^{2}} \leqslant \frac{1}{2}
$$ -/
theorem inequalities_604420 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 / (1 + a ^ 2 + (b + 1) ^ 2) +
    1 / (1 + b ^ 2 + (c + 1) ^ 2) +
    1 / (1 + c ^ 2 + (a + 1) ^ 2) ≤ 1 / 2 := by
  -- Lemma: If a, b are positive real numbers, then
  -- 1 / (1 + a ^ 2 + (b + 1) ^ 2) ≤ 1 / (2 * (1 + a * b + b))
  -- It follows from the fact that a ^ 2 + b ^ 2 ≥ 2 * a * b
  have lem {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    1 / (1 + a ^ 2 + (b + 1) ^ 2) ≤ 1 / (2 * (1 + a * b + b)) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    linarith only [sq_nonneg (a - b)]
  -- Now apply the lemma three times
  have h₁ := lem ha hb
  have h₂ := lem hb hc
  have h₃ := lem hc ha
  -- We can rewrite the terms so that they have the same denominator
  have h₄ : 1 / (2 * (1 + b * c + c)) = a * b / (2 * (1 + a * b + b)) := by
    field_simp
    linear_combination (-(2 * b) - 2) * habc
  have h₅ : 1 / (2 * (1 + c * a + a)) = b / (2 * (1 + a * b + b)) := by
    field_simp
    linear_combination -2 * habc
  -- Now we can add the terms and we are done
  calc
    _ ≤ 1 / (2 * (1 + a * b + b)) + a * b / (2 * (1 + a * b + b)) + b / (2 * (1 + a * b + b)) := by linarith only [h₁, h₂, h₃, h₄, h₅]
    _ = 1 / 2 := by field_simp; ring
