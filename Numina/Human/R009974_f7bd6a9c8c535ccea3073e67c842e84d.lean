import Mathlib

/- For all $x, y, z>0$ satisfying $\frac{x}{y z}+\frac{y}{z x}+\frac{z}{x y} \leq x+y+z$, prove that

$$
\frac{1}{x^{2}+y+z}+\frac{1}{y^{2}+z+x}+\frac{1}{z^{2}+x+y} \leq 1
$$ -/
theorem inequalities_605082 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x / (y * z) + y / (z * x) + z / (x * y) ≤ x + y + z) :
    1 / (x ^ 2 + y + z) + 1 / (y ^ 2 + z + x) + 1 / (z ^ 2 + x + y) ≤ 1 := by
    -- First, prove Cauchy-Schwarz inequality for 3D vectors
    have h1 : ∀ x1 y1 z1 x2 y2 z2 : ℝ, x1 > 0 → y1 > 0 → z1 > 0 → x2 > 0 → y2 > 0 → z2 > 0 →
        (x1 ^ 2 + y1 ^ 2 + z1 ^ 2) * (x2 ^ 2 + y2 ^ 2 + z2 ^ 2) ≥ (x1 * x2 + y1 * y2 + z1 * z2) ^ 2:= by
        intro x1 y1 z1 x2 y2 z2 _ _ _ _ _ _
        -- Use the fact that sum of squares is non-negative
        have h1 : (x1 * y2 - y1 * x2) ^ 2 + (y1 * z2 - z1 * y2) ^ 2 + (z1 * x2 - x1 * z2) ^ 2 ≥ 0:= by positivity
        linarith

    -- Prove a key inequality using Cauchy-Schwarz
    have h2 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → 1 / (x ^ 2 + y + z) ≤ (y ^ 2 + y * z ^ 2 + z * x ^ 2) / (x * y + y * z + z * x) ^ 2:= by
        intro x y z hx hy hz
        -- Apply Cauchy-Schwarz with carefully chosen vectors
        specialize h1 x (√y) (√z) y (√(y * z ^ 2)) (√(z * x ^ 2)) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
        -- Simplify square roots using algebraic properties
        rw [Real.sq_sqrt (by positivity)] at h1
        rw [Real.sq_sqrt (by positivity)] at h1
        rw [Real.sq_sqrt (by positivity)] at h1
        rw [Real.sq_sqrt (by positivity)] at h1
        rw [Eq.symm (Real.sqrt_mul' _ (by positivity))] at h1
        rw [Eq.symm (Real.sqrt_mul' _ (by positivity))] at h1
        rw [show y * (y * z ^ 2) = (y * z) ^ 2 by ring] at h1
        rw [show z * (z * x ^ 2) = (z * x) ^ 2 by ring] at h1
        rw [show √((y * z) ^ 2) = y * z by refine Real.sqrt_sq (by positivity)] at h1
        rw [show √((z * x) ^ 2) = z * x by refine Real.sqrt_sq (by positivity)] at h1
        -- Complete the inequality transformation
        have g1 : (x ^ 2 + y + z) > 0:= by positivity
        replace h1 : y ^ 2 + y * z ^ 2 + z * x ^ 2 ≥ (x * y + y * z + z * x) ^ 2 / (x ^ 2 + y + z):= by exact (div_le_iff₀' g1).mpr h1
        rw [show (x * y + y * z + z * x) ^ 2 / (x ^ 2 + y + z) = (x * y + y * z + z * x) ^ 2 * (1 / (x ^ 2 + y + z)) by ring] at h1
        replace g1 : (x * y + y * z + z * x) ^ 2 > 0:= by positivity
        exact (le_div_iff₀' g1).mpr h1

    -- Apply the key inequality to each term
    have h3:= h2 x y z hx hy hz
    have h4:= h2 y z x hy hz hx
    have h5:= h2 z x y hz hx hy

    -- Normalize expressions by rewriting cyclic permutations
    rw [show y * z + z * x + x * y = x * y + y * z + z * x by ring] at h4
    rw [show z * x + x * y + y * z = x * y + y * z + z * x by ring] at h5

    -- Combine the three inequalities and simplify
    suffices (y ^ 2 + y * z ^ 2 + z * x ^ 2) / (x * y + y * z + z * x) ^ 2 + (z ^ 2 + z * x ^ 2 + x * y ^ 2) / (x * y + y * z + z * x) ^ 2 + (x ^ 2 + x * y ^ 2 + y * z ^ 2) / (x * y + y * z + z * x) ^ 2 ≤ 1 by linarith
    clear h1 h2 h3 h4 h5

    -- Algebraic manipulation to combine fractions
    rw [show (y ^ 2 + y * z ^ 2 + z * x ^ 2) / (x * y + y * z + z * x) ^ 2 + (z ^ 2 + z * x ^ 2 + x * y ^ 2) / (x * y + y * z + z * x) ^ 2 + (x ^ 2 + x * y ^ 2 + y * z ^ 2) / (x * y + y * z + z * x) ^ 2 = (y ^ 2 + y * z ^ 2 + z * x ^ 2 + (z ^ 2 + z * x ^ 2 + x * y ^ 2) + (x ^ 2 + x * y ^ 2 + y * z ^ 2)) / (x * y + y * z + z * x) ^ 2 by ring]
    rw [show y ^ 2 + y * z ^ 2 + z * x ^ 2 + (z ^ 2 + z * x ^ 2 + x * y ^ 2) + (x ^ 2 + x * y ^ 2 + y * z ^ 2) = 2 * (x * y ^ 2 + y * z ^ 2 + z * x ^ 2) + x ^ 2 + y ^ 2 + z ^ 2 by ring]

    -- Final steps using the original inequality
    have g1 : (x * y + y * z + z * x) ^ 2 > 0:= by positivity
    suffices 2 * (x * y ^ 2 + y * z ^ 2 + z * x ^ 2) + x ^ 2 + y ^ 2 + z ^ 2 ≤ (x * y + y * z + z * x) ^ 2 by exact(div_le_one₀ g1).mpr this
    replace g1 : x * y * z > 0:= by positivity
    replace h : (x * y * z) * (x / (y * z) + y / (z * x) + z / (x * y)) ≤ (x * y * z) * (x + y + z):= by exact (mul_le_mul_iff_of_pos_left g1).mpr h
    rw [show x * y * z * (x / (y * z) + y / (z * x) + z / (x * y)) = x ^ 2 + y ^ 2 + z ^ 2 by field_simp ; linarith] at h

    -- Complete the proof using non-negativity of squares
    have h1 : (x - z * x) ^ 2 ≥ 0:= by positivity
    have h2 : (y - x * y) ^ 2 ≥ 0:= by positivity
    have h3 : (z - y * z) ^ 2 ≥ 0:= by positivity
    linarith
