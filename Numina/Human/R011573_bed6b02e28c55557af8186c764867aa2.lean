import Mathlib
/- 3. Prove that for any triple $x$, $y$, $z$ of positive numbers, the inequality

$$
\sqrt{x y z}\left(\frac{2}{x+y}+\frac{2}{y+z}+\frac{2}{z+x}\right) \leqq \sqrt{x}+\sqrt{y}+\sqrt{z} .
$$

holds. Determine when equality occurs. -/
theorem inequalities_260657 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : √(x * y * z) * (2 / (x + y) + 2 / (y + z) + 2 / (z + x)) ≤ √x + √y + √z ∧ (√(x * y * z) * (2 / (x + y) + 2 / (y + z) + 2 / (z + x)) =
√x + √y + √z ↔ x = y ∧ y = z):= by
  -- Helper lemma that establishes a key algebraic identity
  -- For positive a, b, c: √a - √(a*b*c)*(2/(b+c)) = √a/(b+c)*(√b - √c)²
  have h1 : ∀ a b c : ℝ, a > 0 → b > 0 → c > 0 → √a - √(a * b * c) * (2 / (b + c)) = √a / (b + c) * (√b - √c) ^ 2:= by
    intro a b c ha hb hc
    -- Rewrite √(a*b*c) as √a*√b*√c
    rw [show √(a * b * c) = √a * √b * √c by field_simp]
    -- Rearrange the left side of the equation
    rw [show √a - √a * √b * √c * (2 / (b + c))  = √a * (1 - (2 * √b * √c) / (b + c)) by ring]
    -- Simplify the fraction
    rw [show 1 - (2 * √b * √c) / (b + c) = (b + c - 2 * √b * √c) / (b + c) by field_simp]
    -- Use the identity (√b - √c)² = b + c - 2√(bc)
    rw [show b + c - 2 * √b * √c = (√b - √c) ^ 2 by ring_nf ; field_simp ; linarith]
    ring

  -- Apply the helper lemma with different permutations of x, y, z
  have g1:= h1 x y z hx hy hz
  have g2:= h1 y z x hy hz hx
  have g3:= h1 z x y hz hx hy

  -- Rewrite the expressions to ensure consistent ordering of variables
  rw [show y * z * x = x * y * z by ring] at g2
  rw [show z * x * y = x * y * z by ring] at g3

  -- Establish that each term in our decomposition is non-negative
  replace h1 : √x / (y + z) * (√y - √z) ^ 2 ≥ 0:= by positivity
  have h2 : √y / (z + x) * (√z - √x) ^ 2 ≥ 0:= by positivity
  have h3 : √z / (x + y) * (√x - √y) ^ 2 ≥ 0:= by positivity

  -- Establish that denominators are non-zero
  have h4 : √x / (y + z) ≠ 0:= by positivity
  have h5 : √y / (z + x) ≠ 0:= by positivity

  -- Begin constructing the conjunction in the theorem statement
  constructor
  .
    linarith
  .
    constructor
    .
      -- Prove the forward direction of the iff statement
      -- If equality holds, then x = y = z
      intro h
      replace h1 : √x / (y + z) * (√y - √z) ^ 2 = 0:= by linarith
      replace h2 : √y / (z + x) * (√z - √x) ^ 2 = 0:= by linarith
      simp [h4] at h1
      simp [h5] at h2
      replace h1 : √y = √z:= by linarith
      replace h2 : √z = √x:= by linarith
      rw [show x = √x ^ 2 by field_simp, show y = √y ^ 2 by field_simp, show z = √z ^ 2 by field_simp]
      rw [h1, h2]
      simp
    .
      -- Prove the reverse direction of the iff statement
      -- If x = y = z, then equality holds
      rintro ⟨rfl, rfl⟩
      field_simp
      ring_nf
