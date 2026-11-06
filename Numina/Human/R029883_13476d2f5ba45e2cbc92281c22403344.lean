import Mathlib
/- Simplify: $2 \sqrt{1.5+\sqrt{2}}-(1.5+\sqrt{2})$. -/
theorem algebra_611087 : 2 * √(1.5 + √2) - (1.5 + √2) = 1 / 2:= by
  -- Simplify numerical expressions and perform basic arithmetic
  norm_num
  -- Rewrite using the fact that 3/2 + √2 = (1 + √2/2)²
  rw [show 3 / 2 + √2 = (1 + √2 / 2) ^ 2 by ring_nf ; field_simp ; linarith]
  -- Simplify expressions involving fractions and square roots
  field_simp
  -- Normalize ring expressions
  ring_nf
  -- Further simplify field expressions
  field_simp
  -- Complete the proof using linear arithmetic
  linarith
