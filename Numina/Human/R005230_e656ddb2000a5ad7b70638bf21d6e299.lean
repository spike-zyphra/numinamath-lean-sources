import Mathlib

/- Let $a, b, c$ be positive real numbers. Prove that  $$ \frac{(2 a+b+c)^{2}}{2 a^{2}+(b+c)^{2}}+\frac{(2 b+c+a)^{2}}{2 b^{2}+(c+a)^{2}}+\frac{(2 c+a+b)^{2}}{2 c^{2}+(a+b)^{2}} \leq 8 $$ -/
theorem algebra_606376 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (2 * a + b + c) ^ 2 / (2 * a ^ 2 + (b + c) ^ 2) + (2 * b + c + a) ^ 2 / (2 * b ^ 2 + (c + a) ^ 2) + (2 * c + a + b) ^ 2 / (2 * c ^ 2 + (a + b) ^ 2) ≤ 8:= by
  -- Make substitution: x = 3a/(a+b+c), y = 3b/(a+b+c), z = 3c/(a+b+c)
  set x:= 3 * a / (a + b + c) with hx
  set y:= 3 * b / (a + b + c) with hy
  set z:= 3 * c / (a + b + c) with hz
  -- Prove x, y, z are positive since a, b, c are positive
  have hxpos : x > 0 := by positivity
  have hypos : y > 0 := by positivity
  have hzpos : z > 0 := by positivity
  clear_value x y z
  -- Prove x + y + z = 3 from the definitions
  have h : x + y + z = 3 := by
    rw [hx, hy, hz]
    field_simp
    linarith
  -- Transform each fraction in terms of x, y, z
  have g1 : (2 * a + b + c) ^ 2 / (2 * a ^ 2 + (b + c) ^ 2) = (x + 3) ^ 2 / (2 * x ^ 2 + (3 - x) ^ 2):= by
    rw [show 3 - x = y + z by linarith]
    rw [hx, hy, hz]
    field_simp
    ring_nf
  -- Similar transformation for the second fraction
  have g2 : (2 * b + c + a) ^ 2 / (2 * b ^ 2 + (c + a) ^ 2) = (y + 3) ^ 2 / (2 * y ^ 2 + (3 - y) ^ 2):= by
    rw [show 3 - y = z + x by linarith]
    rw [hx, hy, hz]
    field_simp
    ring_nf
  -- Similar transformation for the third fraction
  have g3 : (2 * c + a + b) ^ 2 / (2 * c ^ 2 + (a + b) ^ 2) = (z + 3) ^ 2 / (2 * z ^ 2 + (3 - z) ^ 2):= by
    rw [show 3 - z = x + y by linarith]
    rw [hx, hy, hz]
    field_simp
    ring_nf
  rw [g1, g2, g3]
  clear hx hy hz ha hb hc g1 g2 g3 a b c
  -- Prove key inequality for each term: (x + 3)²/(2x² + (3-x)²) ≤ 1/3(4x + 4)
  have h1 : ∀ x : ℝ, x > 0 → 1 / 3 * (4 * x + 4) ≥ (x + 3) ^ 2 / (2 * x ^ 2 + (3 - x) ^ 2):= by
    intro x hx
    have h1 : 2 * x ^ 2 + (3 - x) ^ 2 > 0:= by positivity
    suffices 1 / 3 * (4 * x + 4) * (2 * x ^ 2 + (3 - x) ^ 2) ≥ (x + 3) ^ 2 / (2 * x ^ 2 + (3 - x) ^ 2) * (2 * x ^ 2 + (3 - x) ^ 2) by exact le_of_mul_le_mul_right this h1
    have h2 : (x + 3) ^ 2 / (2 * x ^ 2 + (3 - x) ^ 2) * (2 * x ^ 2 + (3 - x) ^ 2) = (x + 3) ^ 2:= by field_simp
    rw [h2]
    suffices (x - 1) ^ 2 * (4 * x + 3) ≥ 0 by linarith
    positivity
  -- Apply the inequality to y and z
  have h2:= h1 y hypos
  have h3:= h1 z hzpos
  -- Apply the inequality to x
  replace h1:= h1 x hxpos
  -- Complete the proof using linear arithmetic
  linarith
