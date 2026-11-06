import Mathlib
open Real
/- Let $x, y$ and $z$ be strictly positive real numbers such that $x y + y z + z x = 3$.

Prove that

$$
\frac{x+3}{y+z}+\frac{y+3}{z+x}+\frac{z+3}{x+y}+3 \geqslant 27 \frac{(\√{x}+\√{y}+\√{z})^{2}}{(x+y+z)^{3}}
$$ -/
theorem inequalities_129126 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x * y + y * z + z * x = 3) :
(x + 3) / (y + z) + (y + 3) / (z + x) + (z + 3) / (x + y) + 3 ≥ 27 * ((√x + √y + √z) ^ 2 / (x + y + z) ^ 3):= by
  -- Define s as the sum x + y + z
  set s:= x + y + z with hs
  clear_value s
  -- Rewrite the left side of the inequality using s
  rw [show (x + 3) / (y + z) + (y + 3) / (z + x) + (z + 3) / (x + y) + 3 = (s + 3) * (1 / (y + z) + 1 / (z + x) + 1 / (x + y)) by subst s ; field_simp ; ring_nf]
  -- Cauchy-Schwarz inequality for vectors in ℝ³
  have h1 : ∀ x1 y1 z1 x2 y2 z2 : ℝ, x1 > 0 → y1 > 0 → z1 > 0 → x2 > 0 → y2 > 0 → z2 > 0 →
    (x1 ^ 2 + y1 ^ 2 + z1 ^ 2) * (x2 ^ 2 + y2 ^ 2 + z2 ^ 2) ≥ (x1 * x2 + y1 * y2 + z1 * z2) ^ 2:= by
    intro x1 y1 z1 x2 y2 z2 _ _ _ _ _ _
    have h1 : (x1 * y2 - y1 * x2) ^ 2 + (y1 * z2 - z1 * y2) ^ 2 + (z1 * x2 - x1 * z2) ^ 2 ≥ 0:= by positivity
    linarith
  -- Specialized Cauchy-Schwarz inequality for weighted vectors
  have h2 : ∀ x1 y1 z1 x2 y2 z2 : ℝ, x1 > 0 → y1 > 0 → z1 > 0 → x2 > 0 → y2 > 0 → z2 > 0 →
    (x1 ^ 2 / x2 + y1 ^ 2 / y2 + z1 ^ 2 / z2) * (x2 + y2 + z2) ≥ (x1 + y1 + z1) ^ 2:= by
    intro x1 y1 z1 x2 y2 z2 hx1 hy1 hz1 hx2 hy2 hz2
    -- Simplify square roots of squares
    have g1 : √(x1 ^ 2 / x2) ^ 2 = x1 ^ 2 / x2:= by refine Real.sq_sqrt (by positivity)
    have g2 : √(y1 ^ 2 / y2) ^ 2 = y1 ^ 2 / y2:= by refine Real.sq_sqrt (by positivity)
    have g3 : √(z1 ^ 2 / z2) ^ 2 = z1 ^ 2 / z2:= by refine Real.sq_sqrt (by positivity)
    have g4 : √x2 ^ 2 = x2:= by refine Real.sq_sqrt (by positivity)
    have g5 : √y2 ^ 2 = y2:= by refine Real.sq_sqrt (by positivity)
    have g6 : √z2 ^ 2 = z2:= by refine Real.sq_sqrt (by positivity)
    -- Apply Cauchy-Schwarz to transformed vectors
    have h1:= h1 (√(x1 ^ 2 / x2)) (√(y1 ^ 2 / y2)) (√(z1 ^ 2 / z2)) (√x2) (√y2) (√z2) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    rw [g1, g2, g3, g4, g5, g6] at h1
    -- Simplify expressions involving square roots
    rw [(Eq.symm (Real.sqrt_mul (by positivity) x2)), (show x1 ^ 2 / x2 * x2 = x1 ^ 2 by field_simp), (show √(x1 ^ 2) = x1 by refine Real.sqrt_sq (by positivity))] at h1
    rw [(Eq.symm (Real.sqrt_mul (by positivity) y2)), (show y1 ^ 2 / y2 * y2 = y1 ^ 2 by field_simp), (show √(y1 ^ 2) = y1 by refine Real.sqrt_sq (by positivity))] at h1
    rw [(Eq.symm (Real.sqrt_mul (by positivity) z2)), (show z1 ^ 2 / z2 * z2 = z1 ^ 2 by field_simp), (show √(z1 ^ 2) = z1 by refine Real.sqrt_sq (by positivity))] at h1
    exact h1
  -- Apply the first inequality with specific values
  specialize h1 1 1 1 √x √y √z (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
  -- Apply the second inequality with specific values
  specialize h2 1 1 1 (y + z) (z + x) (x + y) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
  field_simp at h1
  -- Simplify constant expressions
  rw [show (1 : ℝ) ^ 2 = 1 by ring_nf] at h2
  -- Simplify sum of pairwise sums
  rw [show y + z + (z + x) + (x + y) = 2 * (x + y + z) by ring_nf] at h2
  rw [show (1 : ℝ) + 1 + 1 = 3 by ring_nf] at h1
  rw [show ((1 : ℝ) + 1 + 1) ^ 2 = 9 by ring_nf] at h2
  -- Substitute s back into the inequalities
  rw [←hs] at h1 h2
  -- Establish that s + 3 is non-negative
  have g1 : s + 3 ≥ 0:= by subst s ; linarith
  -- Derive inequality for the sum of reciprocals
  replace h2 : 1 / (y + z) + 1 / (z + x) + 1 / (x + y) ≥ 9 / (2 * s):= by exact (div_le_iff₀ (by subst s ; positivity)).mpr h2
  -- Multiply both sides by (s + 3)
  replace h2 : (s + 3) * (1 / (y + z) + 1 / (z + x) + 1 / (x + y)) ≥ (s + 3) * (9 / (2 * s)):= by exact mul_le_mul_of_nonneg_left h2 g1
  -- Establish that s³ is positive
  replace g1 : s ^ 3 > 0:= by subst s ; positivity
  -- Rewrite the right side of the original inequality
  replace h1 : (√x + √y + √z) ^ 2 / s ^ 3 ≤ 3 * s / s ^ 3:= by exact (div_le_div_right g1).mpr h1
  -- Prove that the intermediate inequality implies the original one
  suffices (s + 3) * (9 / (2 * s)) ≥ 27 * (3 * s / s ^ 3) by linarith
  clear h1 h2
  field_simp
  -- Rearrange the inequality
  suffices 27 * (3 * s) ≤ (s + 3) * 9 / (2 * s) * s ^ 3 by exact (div_le_iff₀ g1).mpr this
  replace g1 : s > 0:= by subst s ; linarith
  -- Simplify the right side
  rw [show (s + 3) * 9 / (2 * s) * s ^ 3 = 9 / 2 * s ^ 2 * (s + 3) by field_simp ; linarith]
  -- Reduce to showing s * (s - 3) * (s + 6) ≥ 0
  suffices s * (s - 3) * (s + 6) ≥ 0 by linarith
  -- Prove that s ≥ 3 using the constraint x*y + y*z + z*x = 3
  replace hs : s - 3 ≥ 0:= by
    -- Use the inequality (x+y+z)² ≥ 3(xy+yz+zx)
    have h1 : (x + y + z) ^ 2 ≥ 3 * (x * y + y * z + z * x):= by
      suffices (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 ≥ 0 by linarith
      positivity
    rw [h, ←hs] at h1
    -- Rearrange to show s - 3 ≥ 0
    replace h1 : (s - 3) * (s + 3) ≥ 0:= by linarith
    replace g1 : s + 3 > 0:= by linarith
    exact (mul_nonneg_iff_of_pos_right g1).mp h1
  -- Complete the proof by showing the product is non-negative
  positivity
