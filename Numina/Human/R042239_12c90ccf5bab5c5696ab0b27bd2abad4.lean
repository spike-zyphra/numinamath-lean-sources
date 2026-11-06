import Mathlib
/- Let $a, b, c$ be positive real numbers with $a b c=1$. Prove the inequality:

$$
\frac{2 a^{2}+\frac{1}{a}}{b+\frac{1}{a}+1}+\frac{2 b^{2}+\frac{1}{b}}{c+\frac{1}{b}+1}+\frac{2 c^{2}+\frac{1}{c}}{a+\frac{1}{c}+1} \geq 3
$$ -/
theorem algebra_605824 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : 3 ≤ (2 * a ^ 2 + 1 / a) / (b + 1 / a + 1) + (2 * b ^ 2 + 1 / b) / (c + 1 / b + 1) + (2 * c ^ 2 + 1 / c) / (a + 1 / c + 1) := by
    -- First, prove that for any positive x, 2x² + 1/x ≥ 3x
    have h1 : ∀ x : ℝ, x > 0 → 2 * x ^ 2 + 1 / x ≥ 3 * x:= by
        intro x hx
        suffices (2 * x ^ 2 + 1 / x) * x ≥ 3 * x * x by exact le_of_mul_le_mul_right this hx
        rw [show (2 * x ^ 2 + 1 / x) * x = 2 * x ^ 3 + 1 by field_simp ; linarith]
        suffices 2 * x ^ 3 + 1 - 3 * x ^ 2 ≥ 0 by linarith
        rw [show 2 * x ^ 3 + 1 - 3 * x ^ 2 = (2 * x + 1) * (x - 1) ^ 2 by linarith]
        positivity

    -- Apply the inequality to a, b, and c
    have _:= h1 a ha
    have _:= h1 b hb
    have _:= h1 c hc

    -- Convert the inequalities to fractions
    replace h2 : (2 * a ^ 2 + 1 / a) / (b + 1 / a + 1) ≥ 3 * a / (b + 1 / a + 1):= (div_le_div_right (by positivity)).mpr (h1 a ha)
    replace h3 : (2 * b ^ 2 + 1 / b) / (c + 1 / b + 1) ≥ 3 * b / (c + 1 / b + 1):= (div_le_div_right (by positivity)).mpr (h1 b hb)
    replace h4 : (2 * c ^ 2 + 1 / c) / (a + 1 / c + 1) ≥ 3 * c / (a + 1 / c + 1):= (div_le_div_right (by positivity)).mpr (h1 c hc)

    -- Now we only need to prove that the sum of these three fractions ≥ 3
    suffices 3 * a / (b + 1 / a + 1) + 3 * b / (c + 1 / b + 1) + 3 * c / (a + 1 / c + 1) ≥ 3 by linarith
    clear h1 h2 h3 h4

    -- Use the condition abc = 1 to simplify reciprocals
    rw [show 1 / a = b * c by field_simp ; linarith]
    rw [show 1 / b = a * c by field_simp ; linarith]
    rw [show 1 / c = a * b by field_simp ; linarith]

    -- Simplify fractions through algebraic manipulation
    have g1 : 3 * a / (b + b * c + 1) = 3 * a ^ 2 / (a * b + a + 1):= by
        replace habc : a = 1 / (b * c):= by field_simp ; linarith
        rw [habc]
        field_simp
        linarith
    have g2 : 3 * b / (c + a * c + 1) = 3 * b ^ 2 / (b * c + b + 1):= by
        replace habc : b = 1 / (a * c):= by field_simp ; linarith
        rw [habc]
        field_simp
        linarith
    have g3 : 3 * c / (a + a * b + 1) = 3 * c ^ 2 / (c * a + c + 1):= by
        replace habc : c = 1 / (a * b):= by field_simp ; linarith
        rw [habc]
        field_simp
        linarith
    rw [g1, g2, g3]
    clear g1 g2 g3

    -- Apply Cauchy-Schwarz inequality
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
    specialize h1 a b c (a * b + a + 1) (b * c + b + 1) (c * a + c + 1) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    rw [show a * b + a + 1 + (b * c + b + 1) + (c * a + c + 1) = a + b + c + (a * b + b * c + c * a) + 3 by ring_nf] at h1
    have h2 : a + b + c + (a * b + b * c + c * a) + 3 > 0:= by positivity
    replace h1 : a ^ 2 / (a * b + a + 1) + b ^ 2 / (b * c + b + 1) + c ^ 2 / (c * a + c + 1) ≥ (a + b + c) ^ 2 / (a + b + c + (a * b + b * c + c * a) + 3):= by exact (div_le_iff₀ h2).mpr h1
    rw [show 3 * a ^ 2 / (a * b + a + 1) + 3 * b ^ 2 / (b * c + b + 1) + 3 * c ^ 2 / (c * a + c + 1) = 3 * (a ^ 2 / (a * b + a + 1) + b ^ 2 / (b * c + b + 1) + c ^ 2 / (c * a + c + 1)) by ring]
    suffices (a + b + c) ^ 2 / (a + b + c + (a * b + b * c + c * a) + 3) ≥ 1 by linarith
    clear h1
    suffices (a + b + c) ^ 2 ≥ (a + b + c + (a * b + b * c + c * a) + 3) by exact (one_le_div₀ h2).mpr this
    suffices a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a ≥ a + b + c + 3 by linarith

    -- Apply AM-GM inequality to prove x + y + z ≥ 3(xyz)^(1/3) for positive x, y, z
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
    have h3:= h1 a b c ha hb hc
    have h4:= h1 (a * b) (b * c) (c * a) (by positivity) (by positivity) (by positivity)
    rw [show (a * b) * (b * c) * (c * a) = (a * b * c) ^ 2 by ring_nf] at h4
    rw [habc] at h3 h4
    simp at h3 h4

    -- Final step: prove that sum of squares plus cross terms is greater than sum plus 3
    have h5 : a ^ 2 + b ^ 2 + c ^ 2 + 3 ≥ 2 * a + 2 * b + 2 * c:= by
        have g1 : (a - 1) ^ 2 + (b - 1) ^ 2 + (c - 1) ^ 2 ≥ 0:= by positivity
        linarith
    linarith
