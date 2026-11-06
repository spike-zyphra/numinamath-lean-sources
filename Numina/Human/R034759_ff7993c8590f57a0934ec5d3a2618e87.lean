import Mathlib

/- Let $a . b$ c ce positue real numbers such that $a+b+c=a^{2}+b^{2}+c^{2}$. Shou that

$$
\frac{a^{2}}{a^{2}+a b}+\frac{b^{2}}{b^{2}+b c}+\frac{c^{2}}{c^{2}+c a} \geq \frac{a+b+c}{2}
$$ -/

-- Main theorem: Proves the inequality for positive real numbers a, b, c satisfying the given condition
theorem algebra_604456 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = a ^ 2 + b ^ 2 + c ^ 2) :
  a ^ 2 / (a ^ 2 + a * b) + b ^ 2 / (b ^ 2 + b * c) + c ^ 2 / (c ^ 2 + c * a) ≥ (a + b + c) / 2:= by

  -- Step 1: Prove Cauchy-Schwarz inequality for 3D vectors
  have h1 : ∀ x1 y1 z1 x2 y2 z2 : ℝ, x1 > 0 → y1 > 0 → z1 > 0 → x2 > 0 → y2 > 0 → z2 > 0 →
    (x1 ^ 2 + y1 ^ 2 + z1 ^ 2) * (x2 ^ 2 + y2 ^ 2 + z2 ^ 2) ≥ (x1 * x2 + y1 * y2 + z1 * z2) ^ 2:= by
    intro x1 y1 z1 x2 y2 z2 _ _ _ _ _ _
    have h1 : (x1 * y2 - y1 * x2) ^ 2 + (y1 * z2 - z1 * y2) ^ 2 + (z1 * x2 - x1 * z2) ^ 2 ≥ 0:= by positivity
    linarith
  replace h1 : ∀ x1 y1 z1 x2 y2 z2 : ℝ, x1 > 0 → y1 > 0 → z1 > 0 → x2 > 0 → y2 > 0 → z2 > 0 →
    (x1 ^ 2 / x2 + y1 ^ 2 / y2 + z1 ^ 2 / z2) * (x2 + y2 + z2) ≥ (x1 + y1 + z1) ^ 2:= by
    intro x1 y1 z1 x2 y2 z2 hx1 hy1 hz1 hx2 hy2 hz2
    have g1 : √(x1 ^ 2 / x2) ^ 2 = x1 ^ 2 / x2:= by refine Real.sq_sqrt (by positivity)
    have g2 : √(y1 ^ 2 / y2) ^ 2 = y1 ^ 2 / y2:= by refine Real.sq_sqrt (by positivity)
    have g3 : √(z1 ^ 2 / z2) ^ 2 = z1 ^ 2 / z2:= by refine Real.sq_sqrt (by positivity)
    have g4 : √x2 ^ 2 = x2:= by refine Real.sq_sqrt (by positivity)
    have g5 : √y2 ^ 2 = y2:= by refine Real.sq_sqrt (by positivity)
    have g6 : √z2 ^ 2 = z2:= by refine Real.sq_sqrt (by positivity)
    have h1:= h1 (√(x1 ^ 2 / x2)) (√(y1 ^ 2 / y2)) (√(z1 ^ 2 / z2)) (√x2) (√y2) (√z2) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    rw [g1, g2, g3, g4, g5, g6] at h1
    rw [(Eq.symm (Real.sqrt_mul (by positivity) x2)), (show x1 ^ 2 / x2 * x2 = x1 ^ 2 by field_simp), (show √(x1 ^ 2) = x1 by refine Real.sqrt_sq (by positivity))] at h1
    rw [(Eq.symm (Real.sqrt_mul (by positivity) y2)), (show y1 ^ 2 / y2 * y2 = y1 ^ 2 by field_simp), (show √(y1 ^ 2) = y1 by refine Real.sqrt_sq (by positivity))] at h1
    rw [(Eq.symm (Real.sqrt_mul (by positivity) z2)), (show z1 ^ 2 / z2 * z2 = z1 ^ 2 by field_simp), (show √(z1 ^ 2) = z1 by refine Real.sqrt_sq (by positivity))] at h1
    exact h1
  replace h1:= h1 a b c (a ^ 2 + a * b) (b ^ 2 + b * c) (c ^ 2 + c * a) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)

  -- Step 4: Prove the denominator is positive
  have g1 : a ^ 2 + a * b + (b ^ 2 + b * c) + (c ^ 2 + c * a) > 0:= by positivity

  -- Step 5: Rearrange the inequality using division
  replace h1 : a ^ 2 / (a ^ 2 + a * b) + b ^ 2 / (b ^ 2 + b * c) + c ^ 2 / (c ^ 2 + c * a) ≥
    (a + b + c) ^ 2 / (a ^ 2 + a * b + (b ^ 2 + b * c) + (c ^ 2 + c * a)):= by exact (div_le_iff₀ g1).mpr h1

  -- Step 6: Show that the RHS of previous inequality is ≥ (a + b + c) / 2
  suffices (a + b + c) ^ 2 / (a ^ 2 + a * b + (b ^ 2 + b * c) + (c ^ 2 + c * a)) ≥ (a + b + c) / 2 by linarith

  -- Step 7: Algebraic manipulations and final steps using positivity
  clear g1 h1
  rw [show (a + b + c) ^ 2 / (a ^ 2 + a * b + (b ^ 2 + b * c) + (c ^ 2 + c * a)) = (a + b + c) / (a ^ 2 + a * b + (b ^ 2 + b * c) + (c ^ 2 + c * a)) * (a + b + c) by ring]
  rw [show (a + b + c) / 2 = 1 / 2 * (a + b + c) by ring]
  have g1 : a + b + c > 0:= by positivity
  suffices (a + b + c) / (a ^ 2 + a * b + (b ^ 2 + b * c) + (c ^ 2 + c * a)) ≥ 1 / 2 by exact (mul_le_mul_iff_of_pos_right g1).mpr this
  have g2 : a ^ 2 + a * b + (b ^ 2 + b * c) + (c ^ 2 + c * a) > 0:= by positivity
  suffices a + b + c ≥ 1 / 2 * (a ^ 2 + a * b + (b ^ 2 + b * c) + (c ^ 2 + c * a)) by exact (le_div_iff₀ g2).mpr this

  -- Step 8: Use the fact that (a-b)² + (b-c)² + (c-a)² ≥ 0 to complete the proof
  have h2 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ≥ 0:= by positivity
  linarith
