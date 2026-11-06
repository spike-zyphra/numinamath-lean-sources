import Mathlib

/-
II. (40 points) Let $a, b, c$ be non-negative real numbers. Prove that:
$$
\sum \frac{1}{a^{2}+2 b c+3 a(b+c)} \leqslant \frac{1}{a b+b c+c a},
$$

where, “${ }^{4}$” denotes the cyclic sum.
-/
theorem inequalities_302044
    (a b c : ℝ)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hc : 0 ≤ c)
    (h₁ : a ^ 2 + 2 * b * c + 3 * a * (b + c) ≠ 0)
    (h₂ : b ^ 2 + 2 * c * a + 3 * b * (a + c) ≠ 0)
    (h₃ : c ^ 2 + 2 * a * b + 3 * c * (a + b) ≠ 0)
    (h₄ : a * b + b * c + c * a ≠ 0):
    1 / (a ^ 2 + 2 * b * c + 3 * a * (b + c)) +
    1 / (b ^ 2 + 2 * c * a + 3 * b * (a + c)) +
    1 / (c ^ 2 + 2 * a * b + 3 * c * (a + b)) ≤
    1 / (a * b + b * c + c * a) := by
  -- Simplify the result
  field_simp
  apply div_le_div_iff₀ ?_ ?_ |>.mpr
  · apply sub_nonneg.mp
    ring_nf
    -- After arranging, we get:
    -- a * b * c * ((a - b) ^ 2 * (a + b) + (b - c) ^ 2 * (b + c) + (c - a) ^ 2 * (c + a))
    -- + a * b * c * ((a + b + c) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) / 2)
    -- + a ^ 2 * b ^ 2 * (a - b) ^ 2 + b ^ 2 * c ^ 2 * (b - c) ^ 2 + c ^ 2 * a ^ 2 * (c - a) ^ 2 ≥ 0
    trans a * b * c * ((a - b) ^ 2 * (a + b) + (b - c) ^ 2 * (b + c) + (c - a) ^ 2 * (c + a)) + a * b * c * ((a + b + c) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) / 2) + a ^ 2 * b ^ 2 * (a - b) ^ 2 + b ^ 2 * c ^ 2 * (b - c) ^ 2 + c ^ 2 * a ^ 2 * (c - a) ^ 2
    · -- This is obviously true
      apply add_nonneg ?_ (by positivity)
      apply add_nonneg ?_ (by positivity)
      apply add_nonneg ?_ (by positivity)
      apply add_nonneg
      all_goals positivity
    · apply le_of_eq
      ring
  all_goals positivity
