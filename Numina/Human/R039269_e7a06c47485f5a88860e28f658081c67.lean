import Mathlib

/- Let $a$, $b$ and $c$ be positive real numbers, prove that \[\frac{2a^2 b^2}{a^5+b^5}+\frac{2b^2 c^2}{b^5+c^5}+\frac{2c^2 a^2}{c^5+a^5}\le\frac{a+b}{2ab}+\frac{b+c}{2bc}+\frac{c+a}{2ca}\] -/
theorem inequalities_46346 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    2 * a ^ 2 * b ^ 2 / (a ^ 5 + b ^ 5) + 2 * b ^ 2 * c ^ 2 / (b ^ 5 + c ^ 5) +
    2 * c ^ 2 * a ^ 2 / (c ^ 5 + a ^ 5) ≤
    (a + b) / (2 * a * b) + (b + c) / (2 * b * c) + (c + a) / (2 * c * a) := by 
  have h1 : ∀ x y : ℝ, 0 < x → 0 < y → 2 * x ^ 2 * y ^ 2 / (x ^ 5 + y ^ 5) ≤ (x + y) / (2 * x * y) := by
    intro x y hx hy
    -- Ensure the positivity of expressions dividing squared elements
    have h1 : 0 < x * y := mul_pos hx hy 
    have h2 : 0 < x ^ 2 * y ^ 2 := by positivity 
    have h3 : 0 < x ^ 2 + y ^ 2 := by nlinarith [hx, hy]
    rw [div_le_div_iff (by positivity) (by positivity)]
    -- Rewriting target inequality and expanding terms via polynomial coercive operations
    ring_nf
    nlinarith [sq_nonneg (x ^ 2 - y ^ 2), mul_self_nonneg (x ^ 2 * y ^ 2), sq_nonneg (x * y),
      mul_nonneg (sq_nonneg x) (sq_nonneg y), hx, hy, sq_nonneg (x - y)]
  -- Apply the established lemma into forming triplet instance formula verifying intended reductions.
  linarith [h1 a b ha hb, h1 b c hb hc, h1 c a hc ha]