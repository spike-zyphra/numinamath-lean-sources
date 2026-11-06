import Mathlib
/- Soient $x$, y et $z$ des réels strictement positifs tels que

$$
x+y+z \geqslant \frac{1}{x}+\frac{1}{y}+\frac{1}{z}
$$

Montrer que

$$
\frac{x}{y}+\frac{y}{z}+\frac{z}{x} \geqslant \frac{1}{x y}+\frac{1}{y z}+\frac{1}{z x}
$$ -/
theorem algebra_607474 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z ≥ 1 / x + 1 / y + 1 / z) :
    x / y + y / z + z / x ≥ 1 / (x * y) + 1 / (y * z) + 1 / (z * x):= by
    -- First, we prove Cauchy-Schwarz inequality for 3D vectors
    have h1 : ∀ x1 y1 z1 x2 y2 z2 : ℝ, x1 > 0 → y1 > 0 → z1 > 0 → x2 > 0 → y2 > 0 → z2 > 0 →
        (x1 ^ 2 + y1 ^ 2 + z1 ^ 2) * (x2 ^ 2 + y2 ^ 2 + z2 ^ 2) ≥ (x1 * x2 + y1 * y2 + z1 * z2) ^ 2:= by
        intro x1 y1 z1 x2 y2 z2 _ _ _ _ _ _
        -- This is equivalent to sum of squares being non-negative
        have h1 : (x1 * y2 - y1 * x2) ^ 2 + (y1 * z2 - z1 * y2) ^ 2 + (z1 * x2 - x1 * z2) ^ 2 ≥ 0:= by positivity
        linarith

    -- Apply Cauchy-Schwarz to specific vectors: (√(x²z), √(y²x), √(z²y)) and (√(1/z), √(1/x), √(1/y))
    specialize h1 √(x ^ 2 * z) √(y ^ 2 * x) √(z ^ 2 * y) √(1 / z) √(1 / x) √(1 / y) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)

    -- Series of simplifications using properties of square roots
    rw [Real.sq_sqrt (by positivity)] at h1
    rw [Real.sq_sqrt (by positivity)] at h1
    rw [Real.sq_sqrt (by positivity)] at h1
    rw [Real.sq_sqrt (by positivity)] at h1
    rw [Real.sq_sqrt (by positivity)] at h1
    rw [Real.sq_sqrt (by positivity)] at h1
    rw [Eq.symm (Real.sqrt_mul' _ (by positivity))] at h1
    rw [Eq.symm (Real.sqrt_mul' _ (by positivity))] at h1
    rw [Eq.symm (Real.sqrt_mul' _ (by positivity))] at h1

    -- Algebraic simplifications
    rw [show x ^ 2 * z * (1 / z) = x ^ 2 by field_simp] at h1
    rw [show y ^ 2 * x * (1 / x) = y ^ 2 by field_simp] at h1
    rw [show z ^ 2 * y * (1 / y) = z ^ 2 by field_simp] at h1
    rw [show √(x ^ 2) = x by refine Real.sqrt_sq (by positivity)] at h1
    rw [show √(y ^ 2) = y by refine Real.sqrt_sq (by positivity)] at h1
    rw [show √(z ^ 2) = z by refine Real.sqrt_sq (by positivity)] at h1

    -- Using the hypothesis to establish inequality
    have h2 : (x + y + z) ^ 2 ≥ (x + y + z) * (1 / x + 1 / y + 1 / z):= by
        rw [show (x + y + z) ^ 2 = (x + y + z) * (x + y + z) by ring_nf]
        have g1 : x + y + z ≥ 0:= by linarith
        exact mul_le_mul_of_nonneg_left h g1

    -- Final algebraic manipulations to reach the conclusion
    rw [show 1 / z + 1 / x + 1 / y = 1 / x + 1 / y + 1 / z by linarith] at h1
    replace h1 : (x ^ 2 * z + y ^ 2 * x + z ^ 2 * y) * (1 / x + 1 / y + 1 / z) ≥ (x + y + z) * (1 / x + 1 / y + 1 / z):= by linarith
    clear h2
    have g1 : 1 / x + 1 / y + 1 / z > 0:= by positivity
    replace h1 : x ^ 2 * z + y ^ 2 * x + z ^ 2 * y ≥ x + y + z:= by exact le_of_mul_le_mul_right h1 g1
    replace g1 : x * y * z > 0:= by positivity

    -- Final step: multiply both sides by xyz and simplify
    suffices (x / y + y / z + z / x) * (x * y * z) ≥ (1 / (x * y) + 1 / (y * z) + 1 / (z * x)) * (x * y * z) by exact le_of_mul_le_mul_right this g1
    rw [show (x / y + y / z + z / x) * (x * y * z) = x ^ 2 * z + y ^ 2 * x + z ^ 2 * y by field_simp ; linarith]
    rw [show (1 / (x * y) + 1 / (y * z) + 1 / (z * x)) * (x * y * z) = x + y + z by field_simp ; linarith]
    exact h1
