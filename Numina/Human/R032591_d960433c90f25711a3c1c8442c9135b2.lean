import Mathlib
open Real

/- If $x, y, z$ are positive real numbers, prove that
$(x+y+z)^2(y z+z x+x y)^2 \leq 3\left(y^2+y z+z^2\right)
\left(z^2+z x+x^2\right)\left(x^2+x y+y^2\right)$ -/
theorem inequalities_607832 (x y z : ℝ) (h₀ : 0 < x) (h₁ : 0 < y) (h₂ : 0 < z) :
(x + y + z)^2 * (y * z + z * x + x * y)^2 ≤ 3 * (y^2 + y * z + z^2) *
(z^2 + z * x + x^2) * (x^2 + x * y + y^2) := by
  -- We begin with the observation that
  -- $x^2 + xy + y^2 = \frac{3}{4}(x+y)^2+\frac{1}{4}(x-y)^2\geq \frac{3}{4}(x+y)^2 $.
  have hobs (a b: ℝ) : a^2 + a * b + b^2 ≥ (3 / 4) * (a + b)^2 := by
    calc
      _ = (3 / 4) * (a + b) ^ 2 + (1 / 4) * (a - b)^2 := by ring
      _ ≥ 3 / 4 * (a + b)^2 := by linarith [sq_nonneg (a - b)]
  have hxy := hobs x y
  -- and similar bounds for $y^{2}+y z+z^{2}, z^{2}+z x+x^{2}$.
  have hyz := hobs y z
  have hzx := hobs z x
  -- Thus $3\left(x^{2}+x y+y^{2}\right)\left(y^{2}+y z+z^{2}\right)\left(z^{2}+z x+x^{2}\right) \geq \frac{81}{64}(x+y)^{2}(y+z)^{2}(z+x)^{2} $
  have hr : 3 * (y^2 + y * z + z^2) * (z^2 + z * x + x^2) * (x^2 + x * y + y^2) ≥ (81/64) * ((y+z)^2 * (z+x)^2 * (x+y)^2) := by
    calc
      _ = (x^2 + x * y + y^2) * (3 * (y^2 + y * z + z^2) * (z^2 + z * x + x^2)) := by ring
      _ ≥ (3 / 4) * (x + y)^2 * (3 * (y^2 + y * z + z^2) * (z^2 + z * x + x^2)) := by
        apply mul_le_mul_of_nonneg_right hxy (by positivity)
      _ = (y^2 + y * z + z^2) * (3 * (3 / 4) * (x + y)^2 * (z^2 + z * x + x^2)) := by ring
      _ ≥ (3 / 4) * (y + z)^2 * (3 * (3 / 4) * (x + y)^2 * (z^2 + z * x + x^2)) := by
        apply mul_le_mul_of_nonneg_right hyz (by positivity)
      _ = (z^2 + z * x + x^2) * (3 * (3 / 4) * (y + z)^2 * (3 / 4) * (x + y)^2) := by ring
      _ ≥ (3 / 4) * (z + x)^2 * (3 * (3 / 4) * (y + z)^2 * (3 / 4) * (x + y)^2) := by
        apply mul_le_mul_of_nonneg_right hzx (by positivity)
      _ = (81 / 64) * ((y + z)^2 * (z + x)^2 * (x + y)^2) := by ring
  -- Thus it is sufficient to prove that $(x+y+z)(x y+y z+z x) \leq \frac{9}{8}(x+y)(y+z)(z+x) $
  -- Equivalently, we need to prove that $ 8(x+y+z)(x y+y z+z x) \leq 9(x+y)(y+z)(z+x) $
  -- we note that $(x+y)(y+z)(z+x)=(x+y+z)(y z+z x+x y)-x y z $
  have h1: (y+z) * (z+x) * (x+y) = (x+y+z) * (y * z + z * x + x * y) - x * y * z := by ring
  -- Thus the required inequality takes the form $(x+y)(y+z)(z+x) \geq 8 x y z $
  -- This follows from AM-GM inequalities
  have hamgm {a b: ℝ} (ha: a > 0) (hb: b > 0): a + b ≥ 2 * √(a*b) := by
    apply two_mul_le_add_of_sq_eq_mul (by linarith [ha]) (by linarith [hb])
    calc
      _ = (√ a) ^ 2 * (√ b) ^ 2 := by
        rw [Real.sqrt_mul (by linarith [ha]) b]
        ring
      _ = a * b := by rw [Real.sq_sqrt (by linarith [ha]), Real.sq_sqrt (by linarith [hb])]
  have hxy_amgm := hamgm h₀ h₁
  have hyz_amgm := hamgm h₁ h₂
  have hzx_amgm := hamgm h₂ h₀
  have h2: (y + z) * (z + x) * (x + y) ≥ 8 * (x * y * z) := by
    calc
      _ = (x + y) * ((y + z) * (z + x)) := by ring
      _ ≥ 2 * √(x * y) * ((y + z) * (z + x)) := by
        apply mul_le_mul_of_nonneg_right hxy_amgm (by positivity)
      _ = (y + z) * (2 * √(x * y) * (z + x)) := by ring
      _ ≥ 2 * √(y * z) * (2 * √(x * y) * (z + x)) := by
        apply mul_le_mul_of_nonneg_right hyz_amgm (by positivity)
      _ = (z + x) * (2 * √(y * z) * 2 * √(x * y)) := by ring
      _ ≥ 2 * √(z * x) * (2 * √(y * z) * 2 * √(x * y)) := by
        apply mul_le_mul_of_nonneg_right hzx_amgm (by positivity)
      _ = √(z * x) * √(y * z) * √(x * y) * 8 := by ring
      _ = √(x ^ 2 * y ^ 2 * z ^ 2) * 8 := by
        repeat rw [← Real.sqrt_mul]
        ring_nf
        repeat positivity
      _ = √(x ^ 2) * √(y ^ 2) * √(z ^ 2) * 8 := by
        repeat rw [Real.sqrt_mul]
        repeat positivity
      _ = 8 * (x * y * z) := by
        repeat rw [Real.sqrt_sq]
        ring
        repeat positivity
  -- let's prove that $(x+y+z)(x y+y z+z x) \leq \frac{9}{8}(x+y)(y+z)(z+x) $
  have h3: 8 * ((x + y + z) * (y * z + z * x + x * y)) ≤ 9 * ((y + z) * (z + x) * (x + y)) := by
    rw [show 8 * ((x + y + z) * (y * z + z * x + x * y))
        = 8 * ((x + y + z) * (y * z + z * x + x * y) - x * y * z) + 8 * (x * y * z) by ring,
        ← h1]
    apply le_sub_iff_add_le'.mp
    rw [← sub_mul, show (9 - 8: ℝ) = (1: ℝ) by norm_num]
    simp; exact h2
  have h4: (x + y + z) ^ 2 * (y * z + z * x + x * y) ^ 2 ≤ (81 / 64) * ((y + z) ^ 2 * (z + x) ^ 2 * (x + y) ^ 2) := by
    calc
      _ = ((x + y + z) * (y * z + z * x + x * y)) ^ 2 := by linarith
      _ ≤ ((9 / 8) * ((y + z) * (z + x) * (x + y))) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity) (by linarith [h3])
      _ = (81 / 64) * ((y + z) ^ 2 * (z + x) ^ 2 * (x + y) ^ 2) := by ring
  calc
    _ ≤ (81 / 64) * ((y + z) ^ 2 * (z + x) ^ 2 * (x + y) ^ 2) := by exact h4
    _ ≤ 3 * (y ^ 2 + y * z + z ^ 2) * (z ^ 2 + z * x + x ^ 2) * (x ^ 2 + x * y + y ^ 2) := by
      exact (ge_iff_le.mp hr)
