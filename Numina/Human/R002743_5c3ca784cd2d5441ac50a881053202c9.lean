import Mathlib

/- 
A5 Let $x, y, z$ be positive real numbers. Prove that:

$$
\left(x^{2}+y+1\right)\left(x^{2}+z+1\right)\left(y^{2}+z+1\right)\left(y^{2}+x+1\right)\left(z^{2}+x+1\right)\left(z^{2}+y+1\right) \geq(x+y+z)^{6}
$$ -/
theorem inequalieies_106886
    {x y z : ℝ}
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z) :
    (x + y + z) ^ 6 ≤ (x ^ 2 + y + 1) * (x ^ 2 + z + 1) * (y ^ 2 + z + 1) * (y ^ 2 + x + 1) * (z ^ 2 + x + 1) * (z ^ 2 + y + 1) := by
  -- Applying Cauchy-Schwarz's inequality: $$ \left(x^{2}+y+1\right)\left(z^{2}+y+1\right)=\left(x^{2}+y+1\right)\left(1+y+z^{2}\right) \geq(x+y+z)^{2} $$
  have l_cauchy {x y z : ℝ}
      (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
      (x + y + z) ^ 2 ≤ (x ^ 2 + y + 1) * (z ^ 2 + y + 1) := by
    let f : Fin 3 → ℝ := ![x, √ y, 1]
    let g : Fin 3 → ℝ := ![1, √ y, z]
    convert Finset.sum_mul_sq_le_sq_mul_sq {0, 1, 2} f g
    <;> simp [f, g]
    . rw [← pow_two, Real.sq_sqrt (by positivity), add_assoc]
    . rw [Real.sq_sqrt (by positivity), add_assoc]
    . rw [Real.sq_sqrt (by positivity), add_comm 1, add_comm y]

  -- $$ \left(x^{2}+y+1\right)\left(z^{2}+y+1\right)=\left(x^{2}+y+1\right)\left(1+y+z^{2}\right) \geq(x+y+z)^{2} $$
  have h1 : (x + y + z) ^ 2 ≤ (x ^ 2 + y + 1) * (z ^ 2 + y + 1) := by
    exact l_cauchy hx hy hz

  -- $$ \left(x^{2}+z+1\right)\left(y^{2}+z+1\right) \geq(x+y+z)^{2} $$
  have h2 : (x + y + z) ^ 2 ≤ (x ^ 2 + z + 1) * (y ^ 2 + z + 1) := by
    rw [show x + y + z = x + z + y by ring]
    exact l_cauchy hx hz hy

  -- $$ \left(y^{2}+x+1\right)\left(z^{2}+x+1\right) \geq(x+y+z)^{2} $$
  have h3 : (x + y + z) ^ 2 ≤ (y ^ 2 + x + 1) * (z ^ 2 + x + 1) := by
    rw [show x + y + z = y + x + z by ring]
    exact l_cauchy hy hx hz

  -- Multiplying these three inequalities we get the desired result.
  have {t a b c : ℝ}
      (ht : 0 ≤ t)
      (ha : t ≤ a)
      (hb : t ≤ b)
      (hc : t ≤ c) :
      t ^ 3 ≤ a * b * c := by
    rw [pow_three, ← mul_assoc]
    apply mul_le_mul ?_ hc ht (by nlinarith only [ht, ha, hb])
    apply mul_le_mul ha hb ht (by linarith only [ht, ha])

  rw [show (x + y + z) ^ 6 = ((x + y + z) ^ 2) ^ 3 by ring,
      show (x ^ 2 + y + 1) * (x ^ 2 + z + 1) * (y ^ 2 + z + 1) * (y ^ 2 + x + 1) * (z ^ 2 + x + 1) * (z ^ 2 + y + 1) =
        ((x ^ 2 + y + 1) * (z ^ 2 + y + 1)) *
        ((x ^ 2 + z + 1) * (y ^ 2 + z + 1)) *
        ((y ^ 2 + x + 1) * (z ^ 2 + x + 1)) by ring]
  apply this (by positivity) h1 h2 h3
