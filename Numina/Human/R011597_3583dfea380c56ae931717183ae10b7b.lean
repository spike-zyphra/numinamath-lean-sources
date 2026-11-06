import Mathlib

/- If $a,b,c$ are positive real numbers, prove that  $\frac{a^2b^2}{a+b}+\frac{b^2c^2}{b+c}+\frac{c^2a^2}{c+a}\le \frac{a^3+b^3+c^3}{2}$ -/
theorem inequalities_37992 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a ^ 2 * b ^ 2 / (a + b) + b ^ 2 * c ^ 2 / (b + c) + c ^ 2 * a ^ 2 / (c + a)) ≤
    (a ^ 3 + b ^ 3 + c ^ 3) / 2 := by
  have h1 : 0 < a + b := add_pos ha hb
  have h2 : 0 < b + c := add_pos hb hc
  have h3 : 0 < c + a := add_pos hc ha
  have h4 : 0 < a * b := mul_pos ha hb
  have h5 : 0 < b * c := mul_pos hb hc
  have h6 : 0 < c * a := mul_pos hc ha
  -- Using inequalities and multiply factors are positive
  have h7 :
    a ^ 2 * b ^ 2 / (a + b) ≤ (a ^ 3 + b ^ 3) / 2 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    ring_nf
    nlinarith [sq_nonneg (a - b)] -- leverage that squares of subtract are non neh objected by integer factors employed
  have h8 :
    b ^ 2 * c ^ 2 / (b + c) ≤ (b ^ 3 + c ^ 3) / 2 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    ring_nf
    nlinarith [sq_nonneg (b - c)]
  have h9 :
    c ^ 2 * a ^ 2 / (c + a) ≤ (c ^ 3 + a ^ 3) / 2 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    ring_nf
    nlinarith [sq_nonneg (c - a)]
  nlinarith