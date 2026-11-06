import Mathlib
/- Show that

$$
(x+y+z)\left(\frac{1}{x}+\frac{1}{y}+\frac{1}{z}\right) \geq 4\left(\frac{x}{x y+1}+\frac{y}{y z+1}+\frac{z}{z x+1}\right)^{2}
$$

for any real positive numbers $x, y$ and $z$. -/
theorem algebra_604719 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y + z) * (1 / x + 1 / y + 1 / z) ≥ 4 * (x / (x * y + 1) + y / (y * z + 1) + z / (z * x + 1)) ^ 2 := by
    -- First, prove Cauchy-Schwarz inequality for 3D vectors
    have h1 : ∀ x1 y1 z1 x2 y2 z2 : ℝ, x1 > 0 → y1 > 0 → z1 > 0 → x2 > 0 → y2 > 0 → z2 > 0 →
        (x1 ^ 2 + y1 ^ 2 + z1 ^ 2) * (x2 ^ 2 + y2 ^ 2 + z2 ^ 2) ≥ (x1 * x2 + y1 * y2 + z1 * z2) ^ 2:= by
        intro x1 y1 z1 x2 y2 z2 _ _ _ _ _ _
        -- Use the fact that sum of squares is non-negative
        have h1 : (x1 * y2 - y1 * x2) ^ 2 + (y1 * z2 - z1 * y2) ^ 2 + (z1 * x2 - x1 * z2) ^ 2 ≥ 0:= by positivity
        linarith

    -- Apply Cauchy-Schwarz to specific vectors (√x, √y, √z) and (√(1/y), √(1/z), √(1/x))
    specialize h1 √x √y √z √(1 / y) √(1 / z) √(1 / x) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)

    -- Simplify square roots using Real.sq_sqrt
    rw [Real.sq_sqrt (by positivity)] at h1
    rw [Real.sq_sqrt (by positivity)] at h1
    rw [Real.sq_sqrt (by positivity)] at h1
    rw [Real.sq_sqrt (by positivity)] at h1
    rw [Real.sq_sqrt (by positivity)] at h1
    rw [Real.sq_sqrt (by positivity)] at h1

    -- Simplify products of square roots
    rw [show √x * √(1 / y) = √(x * (1 / y)) by refine Eq.symm (Real.sqrt_mul (by linarith) (1 / y))] at h1
    rw [show √y * √(1 / z) = √(y * (1 / z)) by refine Eq.symm (Real.sqrt_mul (by linarith) (1 / z))] at h1
    rw [show √z * √(1 / x) = √(z * (1 / x)) by refine Eq.symm (Real.sqrt_mul (by linarith) (1 / x))] at h1

    -- Simplify fractions
    rw [show x * (1 / y) = x / y by field_simp] at h1
    rw [show y * (1 / z) = y / z by field_simp] at h1
    rw [show z * (1 / x) = z / x by field_simp] at h1

    -- Rewrite the goal using factor of 4
    rw [show 4 * (x / (x * y + 1) + y / (y * z + 1) + z / (z * x + 1)) ^ 2 = (2 * x / (x * y + 1) + 2 * y / (y * z + 1) + 2 * z / (z * x + 1)) ^ 2 by field_simp ; linarith]

    -- Reduce to comparing squares
    suffices (√(x / y) + √(y / z) + √(z / x)) ^ 2 ≥ (2 * x / (x * y + 1) + 2 * y / (y * z + 1) + 2 * z / (z * x + 1)) ^ 2 by linarith
    suffices |√(x / y) + √(y / z) + √(z / x)| ≥ |2 * x / (x * y + 1) + 2 * y / (y * z + 1) + 2 * z / (z * x + 1)| by exact sq_le_sq.mpr this

    -- Handle absolute values
    rw [abs_of_nonneg (by positivity)]
    rw [abs_of_nonneg (by positivity)]

    -- Prove key inequality for each term
    have h2 : ∀ x y : ℝ, x > 0 → y > 0 → √(x / y) ≥ 2 * x / (x * y + 1) := by
        intro x y hx hy
        field_simp
        have h2 : x * y + 1 > 0:= by positivity
        suffices (x * y + 1) * (2 * x / (x * y + 1)) ≤ (x * y + 1) * (√x / √y) by exact le_of_mul_le_mul_left this h2
        rw [show (x * y + 1) * (2 * x / (x * y + 1)) = 2 * x by field_simp]
        replace h2 : √y > 0 := by positivity
        suffices 2 * x * √y ≤ (x * y + 1) * (√x / √y) * √y by exact le_of_mul_le_mul_right this h2
        rw [show (x * y + 1) * (√x / √y) * √y = (x * y + 1) * √x by field_simp]
        -- Use (√(x*y) - 1)² ≥ 0 to complete the proof
        have h3 : (√(x * y) - 1) ^ 2 ≥ 0:= by positivity
        ring_nf at h3
        rw [Real.sq_sqrt (by positivity)] at h3
        replace h3 : √x * (1 - √(x * y) * 2 + x * y) ≥ 0:= by positivity
        ring_nf at h3
        rw [show √(x * y) = √x * √y by refine Real.sqrt_mul' x (by positivity)] at h3
        rw [show √x * (√x * √y) * 2 = √x ^ 2 * 2 * √y by ring] at h3
        rw [Real.sq_sqrt (by positivity)] at h3
        linarith

    -- Apply the inequality to each pair of variables
    have h3:= h2 x y hx hy
    have h4:= h2 y z hy hz
    have h5:= h2 z x hz hx
    linarith
