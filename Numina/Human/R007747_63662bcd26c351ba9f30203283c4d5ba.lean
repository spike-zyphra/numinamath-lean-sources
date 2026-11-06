import Mathlib
/- Let $a, b, c$ be positive real numbers such that $a b c=1$. Prove that the following inequality holds:

$$
2\left(a^{2}+b^{2}+c^{2}\right)\left(\frac{1}{a^{2}}+\frac{1}{b^{2}}+\frac{1}{c^{2}}\right) \geqslant 3(a+b+c+a b+b c+c a)
$$

(Romania) -/
theorem algebra_605625 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    2 * (a ^ 2 + b ^ 2 + c ^ 2) * (1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2) ≥
    3 * (a + b + c + a * b + b * c + c * a) := by
    -- First lemma: For positive x, y, z, proves x³ + y³ + z³ ≥ 3xyz using the identity
    -- x³ + y³ + z³ - 3xyz = 1/2(x+y+z)((x-y)² + (y-z)² + (z-x)²)
    have h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 ≥ 0:= by
        intro x y z hx hy hz
        have h1 : x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 = 1 / 2 * (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) := by ring_nf
        rw [h1]
        positivity
    replace h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x + y + z - (x * y * z) ^ ((1 : ℝ) / 3) * 3 ≥ 0 := by
        intro x y z hx hy hz
        specialize h1 (x ^ ((1 : ℝ) / 3)) (y ^ ((1 : ℝ) / 3)) (z ^ ((1 : ℝ) / 3)) (by positivity) (by positivity) (by positivity)
        rw [show (x ^ ((1 : ℝ) / 3)) ^ 3 = (x ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) by norm_cast] at h1
        rw [show (y ^ ((1 : ℝ) / 3)) ^ 3 = (y ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) by norm_cast] at h1
        rw [show (z ^ ((1 : ℝ) / 3)) ^ 3 = (z ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) by norm_cast] at h1
        rw [(Eq.symm (Real.rpow_mul (by linarith) (1 / 3) 3))] at h1
        rw [(Eq.symm (Real.rpow_mul (by linarith) (1 / 3) 3))] at h1
        rw [(Eq.symm (Real.rpow_mul (by linarith) (1 / 3) 3))] at h1
        rw [show (1 : ℝ) / 3 * 3 = 1 by ring_nf] at h1
        rw [Eq.symm (Real.mul_rpow (by linarith) (by linarith))] at h1
        rw [Eq.symm (Real.mul_rpow (by positivity) (by linarith))] at h1
        simp at h1
        simp
        linarith
    -- Second lemma: Cauchy-Schwarz inequality for 3D vectors
    -- (x₁² + y₁² + z₁²)(x₂² + y₂² + z₂²) ≥ (x₁x₂ + y₁y₂ + z₁z₂)²
    have h2 : ∀ x1 y1 z1 x2 y2 z2 : ℝ, x1 > 0 → y1 > 0 → z1 > 0 → x2 > 0 → y2 > 0 → z2 > 0 →
        (x1 ^ 2 + y1 ^ 2 + z1 ^ 2) * (x2 ^ 2 + y2 ^ 2 + z2 ^ 2) ≥ (x1 * x2 + y1 * y2 + z1 * z2) ^ 2:= by
        intro x1 y1 z1 x2 y2 z2 _ _ _ _ _ _
        have h1 : (x1 * y2 - y1 * x2) ^ 2 + (y1 * z2 - z1 * y2) ^ 2 + (z1 * x2 - x1 * z2) ^ 2 ≥ 0:= by positivity
        linarith
    -- Proves that a/b + b/c + c/a ≥ ab + bc + ca using the first lemma
    have h3 : a / b + b / c + c / a ≥ a * b + b * c + c * a:= by
        have g1:= h1 (a / b) (a / b) (c / a) (by positivity) (by positivity) (by positivity)
        have g2:= h1 (b / c) (b / c) (a / b) (by positivity) (by positivity) (by positivity)
        have g3:= h1 (c / a) (c / a) (b / c) (by positivity) (by positivity) (by positivity)
        rw [show a / b * (a / b) * (c / a) = (a * b * c) * (1 / b) ^ 3 by field_simp ; linarith] at g1
        rw [show b / c * (b / c) * (a / b) = (a * b * c) * (1 / c) ^ 3 by field_simp ; linarith] at g2
        rw [show c / a * (c / a) * (b / c) = (a * b * c) * (1 / a) ^ 3 by field_simp ; linarith] at g3
        rw [Real.mul_rpow (by positivity) (by positivity)] at g1 g2 g3
        rw [show (1 / b) ^ 3 = (1 / b) ^ (3 : ℝ) by norm_cast] at g1
        rw [show (1 / c) ^ 3 = (1 / c) ^ (3 : ℝ) by norm_cast] at g2
        rw [show (1 / a) ^ 3 = (1 / a) ^ (3 : ℝ) by norm_cast] at g3
        rw [Eq.symm (Real.rpow_mul (by positivity) 3 (1 / 3))] at g1 g2 g3
        rw [show 3 * ((1 : ℝ) / 3) = 1 by ring_nf] at g1 g2 g3
        rw [habc] at g1 g2 g3
        simp at g1 g2 g3
        rw [show b⁻¹ = 1 / b by field_simp] at g1
        rw [show c⁻¹ = 1 / c by field_simp] at g2
        rw [show a⁻¹ = 1 / a by field_simp] at g3
        rw [←habc] at g1 g2 g3
        rw [show a * b * c / b = a * c by field_simp ; linarith] at g1
        rw [show a * b * c / c = a * b by field_simp] at g2
        rw [show a * b * c / a = b * c by field_simp ; linarith] at g3
        linarith
    -- Proves that a/b + b/c + c/a ≥ a + b + c using the first lemma
    have h4 : a / b + b / c + c / a ≥ a + b + c:= by
        have g1:= h1 (a / b) (a / b) (b / c) (by positivity) (by positivity) (by positivity)
        have g2:= h1 (b / c) (b / c) (c / a) (by positivity) (by positivity) (by positivity)
        have g3:= h1 (c / a) (c / a) (a / b) (by positivity) (by positivity) (by positivity)
        rw [show a / b * (a / b) * (b / c) = a ^ 3 * (1 / (a * b * c)) by field_simp ; linarith] at g1
        rw [show b / c * (b / c) * (c / a) = b ^ 3 * (1 / (a * b * c)) by field_simp ; linarith] at g2
        rw [show c / a * (c / a) * (a / b) = c ^ 3 * (1 / (a * b * c)) by field_simp ; linarith] at g3
        rw [Real.mul_rpow (by positivity) (by positivity)] at g1 g2 g3
        rw [show a ^ 3 = a ^ (3 : ℝ) by norm_cast] at g1
        rw [show b ^ 3 = b ^ (3 : ℝ) by norm_cast] at g2
        rw [show c ^ 3 = c ^ (3 : ℝ) by norm_cast] at g3
        rw [Eq.symm (Real.rpow_mul (by positivity) 3 (1 / 3))] at g1 g2 g3
        rw [show 3 * ((1 : ℝ) / 3) = 1 by ring_nf] at g1 g2 g3
        rw [habc] at g1 g2 g3
        simp at g1 g2 g3
        linarith
    -- Applies Cauchy-Schwarz inequality with specific vectors
    have h5:= h2 a b c (1 / b) (1 / c) (1 / a) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    rw [show (1 / b) ^ 2 + (1 / c) ^ 2 + (1 / a) ^ 2 = 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 by field_simp ; linarith] at h5
    rw [show a * (1 / b) + b * (1 / c) + c * (1 / a) = a / b + b / c + c / a by field_simp] at h5
    specialize h2 a b c (1 / a) (1 / b) (1 / c) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    rw [show (1 / a) ^ 2 + (1 / b) ^ 2 + (1 / c) ^ 2 = 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 by field_simp] at h2
    rw [show (a * (1 / a) + b * (1 / b) + c * (1 / c)) ^ 2 = 9 by field_simp ; linarith] at h2
    -- Uses the fact that (a/b + b/c + c/a - 3)² ≥ 0 to complete the proof
    have h6 : (a / b + b / c + c / a - 3) ^ 2 ≥ 0:= by positivity
    linarith
