import Mathlib

/- Montrer qu'il n'existe pas de réels $x, y, z$ strictement positifs tels que

$$
\left(2 x^{2}+y z\right)\left(2 y^{2}+x z\right)\left(2 z^{2}+x y\right)=26 x^{2} y^{2} z^{2}
$$
-/
theorem algebra_607160 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : (2 * x ^ 2 + y * z) * (2 * y ^ 2 + x * z) * (2 * z ^ 2 + x * y) = 26 * x ^ 2 * y ^ 2 * z ^ 2) :
    False := by
    -- First, prove a key inequality: For positive reals, x³ + y³ + z³ - 3xyz ≥ 0
    have h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 ≥ 0:= by
        intro x y z hx hy hz
        -- Express the inequality using squares of differences
        have h1 : x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 = 1 / 2 * (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) := by ring_nf
        rw [h1]
        positivity

    -- Transform the inequality using cube roots: x + y + z - 3(xyz)^(1/3) ≥ 0
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
    -- Apply the inequality to three specific cases:
    -- Case 1: (x², x², yz)
    have h2:= h1 (x ^ 2) (x ^ 2) (y * z) (by positivity) (by positivity) (by positivity)
    -- Case 2: (y², y², xz)
    have h3:= h1 (y ^ 2) (y ^ 2) (x * z) (by positivity) (by positivity) (by positivity)
    -- Case 3: (z², z², xy)
    have h4:= h1 (z ^ 2) (z ^ 2) (x * y) (by positivity) (by positivity) (by positivity)

    -- Simplify the expressions
    rw [show x ^ 2 * x ^ 2 * (y * z) = x ^ 4 * y * z by ring] at h2
    rw [show y ^ 2 * y ^ 2 * (x * z) = y ^ 4 * x * z by ring] at h3
    rw [show z ^ 2 * z ^ 2 * (x * y) = z ^ 4 * x * y by ring] at h4

    -- Rearrange the inequalities
    replace h2 :  x ^ 2 + x ^ 2 + y * z ≥ (x ^ 4 * y * z) ^ ((1 : ℝ) / 3) * 3:= by linarith
    replace h3 :  y ^ 2 + y ^ 2 + x * z ≥ (y ^ 4 * x * z) ^ ((1 : ℝ) / 3) * 3:= by linarith
    replace h4 :  z ^ 2 + z ^ 2 + x * y ≥ (z ^ 4 * x * y) ^ ((1 : ℝ) / 3) * 3:= by linarith

    -- Establish positivity for multiplication
    have g1 : (x ^ 4 * y * z) ^ ((1 : ℝ) / 3) * 3 ≥ 0:= by positivity
    have g2 : ((x ^ 4 * y * z) ^ ((1 : ℝ) / 3) * 3) * ((y ^ 4 * x * z) ^ ((1 : ℝ) / 3) * 3) ≥ 0:= by positivity

    -- Multiply the inequalities
    have h5 : (x ^ 2 + x ^ 2 + y * z) * (y ^ 2 + y ^ 2 + x * z) ≥ ((x ^ 4 * y * z) ^ ((1 : ℝ) / 3) * 3) * ((y ^ 4 * x * z) ^ ((1 : ℝ) / 3) * 3):= by refine mul_le_mul_of_nonneg h2 h3 g1 (by positivity)
    have h6 : (x ^ 2 + x ^ 2 + y * z) * (y ^ 2 + y ^ 2 + x * z) * (z ^ 2 + z ^ 2 + x * y) ≥ ((x ^ 4 * y * z) ^ ((1 : ℝ) / 3) * 3) * ((y ^ 4 * x * z) ^ ((1 : ℝ) / 3) * 3) * ((z ^ 4 * x * y) ^ ((1 : ℝ) / 3) * 3):= by refine mul_le_mul_of_nonneg h5 h4 g2 (by positivity)

    -- Clean up unused hypotheses
    clear h1 h2 h3 h4 h5 g1 g2

    -- Final algebraic manipulations to reach contradiction
    rw [show x ^ 2 + x ^ 2 + y * z = 2 * x ^ 2 + y * z by ring_nf] at h6
    rw [show y ^ 2 + y ^ 2 + x * z = 2 * y ^ 2 + x * z by ring_nf] at h6
    rw [show z ^ 2 + z ^ 2 + x * y = 2 * z ^ 2 + x * y by ring_nf] at h6
    rw [show (x ^ 4 * y * z) ^ ((1 : ℝ) / 3) * 3 * ((y ^ 4 * x * z) ^ ((1 : ℝ) / 3) * 3) * ((z ^ 4 * x * y) ^ ((1 : ℝ) / 3) * 3) =
    (x ^ 4 * y * z) ^ ((1 : ℝ) / 3) * (y ^ 4 * x * z) ^ ((1 : ℝ) / 3) * (z ^ 4 * x * y) ^ ((1 : ℝ) / 3) * 27 by ring] at h6
    rw [show (x ^ 4 * y * z) ^ ((1 : ℝ) / 3) * (y ^ 4 * x * z) ^ ((1 : ℝ) / 3) = (x ^ 4 * y * z * (y ^ 4 * x * z)) ^ ((1 : ℝ) / 3)
     by refine Eq.symm (Real.mul_rpow (by positivity) (by positivity))] at h6
    rw [Eq.symm (Real.mul_rpow (by positivity) (by positivity))] at h6
    rw [show x ^ 4 * y * z * (y ^ 4 * x * z) * (z ^ 4 * x * y) = (x ^ 2 * y ^ 2 * z ^ 2) ^ 3 by ring] at h6
    rw [show (x ^ 2 * y ^ 2 * z ^ 2) ^ 3 = (x ^ 2 * y ^ 2 * z ^ 2) ^ (3 : ℝ) by norm_cast] at h6
    rw [show ((x ^ 2 * y ^ 2 * z ^ 2) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) = (x ^ 2 * y ^ 2 * z ^ 2) ^ ((3 : ℝ) * (1 / 3)) by refine Eq.symm (Real.rpow_mul (by positivity) 3 (1 / 3))] at h6
    rw [show (3 : ℝ) * (1 / 3) = 1 by ring_nf] at h6
    simp at h6
    have hpos : x ^ 2 * y ^ 2 * z ^ 2 > 0:= by positivity
    linarith  -- Derive contradiction from the inequalities
