import Mathlib
open Real
/- Let $ a, b, c $ be positive real numbers less than or equal to $ \sqrt{2} $ such that $ abc = 2 $, prove that $$ \sqrt{2}\displaystyle\sum_{cyc}\frac{ab + 3c}{3ab + c} \ge a + b + c $$ -/
theorem inequalities_79176 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
(ha1 : a ≤ √2) (hb1 : b ≤ √2) (hc1 : c ≤ √2) (h : a * b * c = 2) :
√2 * (a * b + 3 * c) / (3 * a * b + c) + √2 * (b * c + 3 * a) / (3 * b * c + a) +√2 * (c * a + 3 * b) / (3 * c * a + b) ≥ a + b + c:= by
  -- Derive ab = 2/c from abc = 2
  have h1 : a * b = 2 / c:= by field_simp ; linarith
  -- Derive bc = 2/a from abc = 2
  have h2 : b * c = 2 / a:= by field_simp ; linarith
  -- Derive ca = 2/b from abc = 2
  have h3 : c * a = 2 / b:= by field_simp ; linarith

  -- Rewrite 3*b*c as 3*(b*c) for easier substitution
  rw [show 3 * b * c = 3 * (b * c) by ring]
  -- Rewrite 3*a*b as 3*(a*b) for easier substitution
  rw [show 3 * a * b = 3 * (a * b) by ring]
  -- Rewrite 3*c*a as 3*(c*a) for easier substitution
  rw [show 3 * c * a = 3 * (c * a) by ring]

  -- Substitute a*b = 2/c and simplify the first term
  rw [show √2 * (a * b + 3 * c) / (3 * (a * b) + c) = √2 * ((2 + 3 * c ^ 2) / (6 + c ^ 2)) by rw [h1] ; field_simp ; linarith]
  -- Substitute b*c = 2/a and simplify the second term
  rw [show √2 * (b * c + 3 * a) / (3 * (b * c) + a) = √2 * ((2 + 3 * a ^ 2) / (6 + a ^ 2)) by rw [h2] ; field_simp ; linarith]
  -- Substitute c*a = 2/b and simplify the third term
  rw [show √2 * (c * a + 3 * b) / (3 * (c * a) + b) = √2 * ((2 + 3 * b ^ 2) / (6 + b ^ 2)) by rw [h3] ; field_simp ; linarith]

  -- Prove a key lemma: for any x ≤ √2, √2*((2+3x²)/(6+x²)) - x ≥ 0
  replace h1 : ∀ x : ℝ, x ≤ √2 → √2 * ((2 + 3 * x ^ 2) / (6 + x ^ 2)) - x ≥ 0:= by
    intro x hx
    -- Rewrite the expression as (√2-x)³/(6+x²) which is clearly non-negative when x ≤ √2
    rw [show √2 * ((2 + 3 * x ^ 2) / (6 + x ^ 2)) - x = (√2 - x) ^ 3 / (6 + x ^ 2) by field_simp ; ring_nf ; rw [show √2 ^ 3 = √2 ^ 2 * √2 by ring_nf] ; field_simp ; ring_nf]
    -- Confirm that √2 - x ≥ 0 from the assumption x ≤ √2
    replace hx : √2 - x ≥ 0:= by linarith
    -- Since (√2-x)³/(6+x²) is a non-negative number divided by a positive number, the result is non-negative
    positivity

  -- Apply the lemma to b
  replace h2:= h1 b hb1
  -- Apply the lemma to c
  replace h3:= h1 c hc1
  -- Apply the lemma to a
  replace h1:= h1 a ha1
  -- Combine the three inequalities to prove the original statement
  linarith
