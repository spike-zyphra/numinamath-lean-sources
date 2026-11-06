import Mathlib
/- For $a, b, c>0$ prove that  $$ \frac{a^{3}+3 b^{3}}{5 a+b}+\frac{b^{3}+3 c^{3}}{5 b+c}+\frac{c^{3}+3 a^{3}}{5 c+a} \geq \frac{2}{3}\left(a^{2}+b^{2}+c^{2}\right) $$ -/
theorem algebra_604441 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    2 / 3 * (a ^ 2 + b ^ 2 + c ^ 2) ≤
    (a ^ 3 + 3 * b ^ 3) / (5 * a + b) + (b ^ 3 + 3 * c ^ 3) / (5 * b + c) +
    (c ^ 3 + 3 * a ^ 3) / (5 * c + a) := by
    -- First key lemma: Cauchy-Schwarz inequality in 3D
    -- (x₁² + y₁² + z₁²)(x₂² + y₂² + z₂²) ≥ (x₁x₂ + y₁y₂ + z₁z₂)²
    have h1 : ∀ x1 y1 z1 x2 y2 z2 : ℝ, x1 > 0 → y1 > 0 → z1 > 0 → x2 > 0 → y2 > 0 → z2 > 0 →
        (x1 ^ 2 + y1 ^ 2 + z1 ^ 2) * (x2 ^ 2 + y2 ^ 2 + z2 ^ 2) ≥ (x1 * x2 + y1 * y2 + z1 * z2) ^ 2:= by
        intro x1 y1 z1 x2 y2 z2 _ _ _ _ _ _
        have h1 : (x1 * y2 - y1 * x2) ^ 2 + (y1 * z2 - z1 * y2) ^ 2 + (z1 * x2 - x1 * z2) ^ 2 ≥ 0:= by positivity
        linarith
    -- Second key lemma: A weighted version of Cauchy-Schwarz
    -- (x₁²/x₂ + y₁²/y₂ + z₁²/z₂)(x₂ + y₂ + z₂) ≥ (x₁ + y₁ + z₁)²
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

    have h2 : (a ^ 3 + 3 * b ^ 3) / (5 * a + b) = (a ^ 2) ^ 2 / (5 * a ^ 2 + a * b) + 3 * (b ^ 2) ^ 2 / (5 * a * b + b ^ 2):= by
        field_simp
        ring_nf

    have h3 : (b ^ 3 + 3 * c ^ 3) / (5 * b + c) = (b ^ 2) ^ 2 / (5 * b ^ 2 + b * c) + 3 * (c ^ 2) ^ 2 / (5 * b * c + c ^ 2):= by
        field_simp
        ring_nf

    have h4 : (c ^ 3 + 3 * a ^ 3) / (5 * c + a) = (c ^ 2) ^ 2 / (5 * c ^ 2 + c * a) + 3 * (a ^ 2) ^ 2 / (5 * c * a + a ^ 2):= by
        field_simp
        ring_nf
    rw [h2, h3, h4]
    clear h2 h3 h4
    -- Split each fraction into two parts using partial fraction decomposition
    have h2:= h1 (a ^ 2) (b ^ 2) (c ^ 2) (5 * a ^ 2 + a * b) (5 * b ^ 2 + b * c) (5 * c ^ 2 + c * a) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    -- Apply weighted Cauchy-Schwarz inequality to both parts
    have h3:= h1 (b ^ 2) (c ^ 2) (a ^ 2) (5 * a * b + b ^ 2) (5 * b * c + c ^ 2) (5 * c * a + a ^ 2
    ) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    -- Verify positivity of denominators
    have h4 : 5 * a ^ 2 + a * b + (5 * b ^ 2 + b * c) + (5 * c ^ 2 + c * a) > 0:= by positivity
    have h5 : 5 * a * b + b ^ 2 + (5 * b * c + c ^ 2) + (5 * c * a + a ^ 2) > 0:= by positivity
    replace h4 : (a ^ 2) ^ 2 / (5 * a ^ 2 + a * b) + (b ^ 2) ^ 2 / (5 * b ^ 2 + b * c) + (c ^ 2) ^ 2 / (5 * c ^ 2 + c * a) ≥ (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 / (5 * a ^ 2 + a * b + (5 * b ^ 2 + b * c) + (5 * c ^ 2 + c * a)):= by exact (div_le_iff₀ h4).mpr h2
    replace h5 : (b ^ 2) ^ 2 / (5 * a * b + b ^ 2) + (c ^ 2) ^ 2 / (5 * b * c + c ^ 2) + (a ^ 2) ^ 2 / (5 * c * a + a ^ 2) ≥ (b ^ 2 + c ^ 2 + a ^ 2) ^ 2 / (5 * a * b + b ^ 2 + (5 * b * c + c ^ 2) + (5 * c * a + a ^ 2)):= by exact (div_le_iff₀ h5).mpr h3
    clear h2 h3
    -- Use the fact that (a-b)² + (b-c)² + (c-a)² ≥ 0 to prove the final bound
    have h2 : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 / (5 * a ^ 2 + a * b + (5 * b ^ 2 + b * c) + (5 * c ^ 2 + c * a)) ≥ (a ^ 2 + b ^ 2 + c ^ 2) * (1 / 6):= by
        have h2 : 5 * a ^ 2 + a * b + (5 * b ^ 2 + b * c) + (5 * c ^ 2 + c * a) > 0:= by positivity
        suffices (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ (a ^ 2 + b ^ 2 + c ^ 2) * (1 / 6) * (5 * a ^ 2 + a * b + (5 * b ^ 2 + b * c) + (5 * c ^ 2 + c * a)) by exact (le_div_iff₀ h2).mpr this
        replace h2 : a ^ 2 + b ^ 2 + c ^ 2 ≥ 0:= by positivity
        rw [show (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 = (a ^ 2 + b ^ 2 + c ^ 2) * (a ^ 2 + b ^ 2 + c ^ 2) by ring_nf]
        rw [show (a ^ 2 + b ^ 2 + c ^ 2) * (1 / 6) * (5 * a ^ 2 + a * b + (5 * b ^ 2 + b * c) + (5 * c ^ 2 + c * a)) =
        (a ^ 2 + b ^ 2 + c ^ 2) * ((1 / 6) * (5 * a ^ 2 + a * b + (5 * b ^ 2 + b * c) + (5 * c ^ 2 + c * a))) by ring]
        suffices (a ^ 2 + b ^ 2 + c ^ 2) ≥ (1 / 6) * (5 * a ^ 2 + a * b + (5 * b ^ 2 + b * c) + (5 * c ^ 2 + c * a)) by exact mul_le_mul_of_nonneg_left this h2
        have h3 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ≥ 0:= by positivity
        linarith only [h3]
    have h3 : (b ^ 2 + c ^ 2 + a ^ 2) ^ 2 / (5 * a * b + b ^ 2 + (5 * b * c + c ^ 2) + (5 * c * a + a ^ 2)) ≥ (b ^ 2 + c ^ 2 + a ^ 2) * (1 / 6):= by
        have h3 : 5 * a * b + b ^ 2 + (5 * b * c + c ^ 2) + (5 * c * a + a ^ 2) > 0:= by positivity
        suffices (b ^ 2 + c ^ 2 + a ^ 2) ^ 2 ≥ (b ^ 2 + c ^ 2 + a ^ 2) * (1 / 6) * (5 * a * b + b ^ 2 + (5 * b * c + c ^ 2) + (5 * c * a + a ^ 2)) by exact (le_div_iff₀ h3).mpr this
        replace h3 : b ^ 2 + c ^ 2 + a ^ 2 ≥ 0:= by positivity
        rw [show (b ^ 2 + c ^ 2 + a ^ 2) ^ 2 = (b ^ 2 + c ^ 2 + a ^ 2) * (b ^ 2 + c ^ 2 + a ^ 2) by ring_nf]
        rw [show (b ^ 2 + c ^ 2 + a ^ 2) * (1 / 6) * (5 * a * b + b ^ 2 + (5 * b * c + c ^ 2) + (5 * c * a + a ^ 2)) =
        (b ^ 2 + c ^ 2 + a ^ 2) * ((1 / 6) * (5 * a * b + b ^ 2 + (5 * b * c + c ^ 2) + (5 * c * a + a ^ 2))) by ring]
        suffices (b ^ 2 + c ^ 2 + a ^ 2) ≥ (1 / 6) * (5 * a * b + b ^ 2 + (5 * b * c + c ^ 2) + (5 * c * a + a ^ 2)) by exact mul_le_mul_of_nonneg_left this h3
        have h4 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ≥ 0:= by positivity
        linarith only [h4]
    -- refine the terms
    rw [show 3 * (b ^ 2) ^ 2 / (5 * a * b + b ^ 2) = 3 * ((b ^ 2) ^ 2 / (5 * a * b + b ^ 2)) by ring]
    rw [show 3 * (c ^ 2) ^ 2 / (5 * b * c + c ^ 2) = 3 * ((c ^ 2) ^ 2 / (5 * b * c + c ^ 2)) by ring]
    rw [show 3 * (a ^ 2) ^ 2 / (5 * c * a + a ^ 2) = 3 * ((a ^ 2) ^ 2 / (5 * c * a + a ^ 2)) by ring]
    -- Combine all inequalities to complete the proof
    linarith
