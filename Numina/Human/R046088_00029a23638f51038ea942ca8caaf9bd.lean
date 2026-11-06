import Mathlib
open Real
/- 165. Prove that

$$
\frac{2+\sqrt{3}}{\sqrt{2}+\sqrt{2+\sqrt{3}}}+\frac{2-\sqrt{3}}{\sqrt{2}-\sqrt{2-\sqrt{3}}}=\sqrt{2}
$$ -/
theorem algebra_276300 : (2 + √3) / (√2 + √(2 + √3)) + (2 - √3) / (√2 - √(2 - √3)) = √2:= by
  -- Express √(2 + √3) in terms of √2 and √3
  have h1 : √(2 + √3) = √2 / 2 * (√3 + 1):= by
    rw [show 2 + √3 = (√2 / 2 * (√3 + 1)) ^ 2 by ring_nf ; field_simp ; linarith]
    field_simp

  -- Express √(2 - √3) in terms of √2 and √3
  have h2 : √(2 - √3) = √2 / 2 * (√3 - 1):= by
    -- Prove that √3 > 1 to ensure √3 - 1 > 0
    have g1 : √3 > 1:= by
      by_contra H
      simp at H
    replace g1 : √3 - 1 > 0:= by linarith
    rw [show 2 - √3 = (√2 / 2 * (√3 - 1)) ^ 2 by ring_nf ; field_simp ; linarith]
    field_simp

  -- Simplify the denominator of the first fraction
  replace h1 : √2 + √(2 + √3) = √2 / 2 * (3 + √3):= by linarith

  -- Simplify the denominator of the second fraction
  replace h2 : √2 - √(2 - √3) = √2 / 2 * (3 - √3):= by linarith

  -- Calculate the reciprocal of the first denominator
  have h3 : 1 / (√2 / 2 * (3 + √3)) = √2 * (3 - √3) / 6:= by
    field_simp
    ring_nf
    field_simp
    linarith

  -- Calculate the reciprocal of the second denominator
  have h4 : 1 / (√2 / 2 * (3 - √3)) = √2 * (3 + √3) / 6:= by
    -- Prove that 3 > √3 to ensure 3 - √3 > 0
    have g1 : 3 > √3:= by
      by_contra H
      simp at H
      replace H : 3 ^ 2 ≤ √3 ^ 2:= by nlinarith only [H]
      field_simp at H
      linarith
    replace g1 : 3 - √3 > 0:= by linarith
    field_simp
    ring_nf
    field_simp
    linarith

  -- Rewrite the first fraction to use the reciprocal of the denominator
  rw [show (2 + √3) / (√2 + √(2 + √3)) = (2 + √3) * (1 / (√2 + √(2 + √3))) by ring]

  -- Rewrite the second fraction to use the reciprocal of the denominator
  rw [show (2 - √3) / (√2 - √(2 - √3)) = (2 - √3) * (1 / (√2 - √(2 - √3))) by ring]

  -- Substitute the simplified expressions
  rw [h1, h2, h3, h4]

  -- Simplify the resulting expression
  ring_nf
  field_simp
  linarith
