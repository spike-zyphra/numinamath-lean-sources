import Mathlib
/- Vind de kleinst mogelijke waarde van

$$
x y+y z+z x+\frac{1}{x}+\frac{2}{y}+\frac{5}{z},
$$

voor positieve reële getallen $x, y$ en $z$. -/
theorem algebra_605668 : IsLeast {x : ℝ | ∃ a b c, x = a * b + b * c + c * a + 1 / a + 2 / b + 5 / c ∧ a > 0 ∧ b > 0 ∧ c > 0} (3 * (36 ^ ((1 : ℝ) / 3))):= by
  constructor
  -- First part: Prove that the given value is achievable
  .
    -- Use the optimal values: x = 6^(1/3)/3, y = 6^(1/3)/2, z = 6^(1/3)
    use (6 ^ ((1 : ℝ) / 3) / 3)
    use (6 ^ ((1 : ℝ) / 3) / 2)
    use (6 ^ ((1 : ℝ) / 3))
    field_simp
    ring_nf
    rw [show (36 : ℝ) = 6 ^ 2 by ring]
    rw [show (6 : ℝ) ^ 2 = 6 ^ (2 : ℝ) by norm_cast]
    rw [Eq.symm (Real.rpow_mul (by linarith) 2 (1 / 3))]
    rw [show ((6 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = ((6 : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) by norm_cast]
    rw [Eq.symm (Real.rpow_mul (by linarith) (1 / 3) 3)]
    rw [show ((6 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 = ((6 : ℝ) ^ ((1 : ℝ) / 3)) ^ (2 : ℝ) by norm_cast]
    rw [Eq.symm (Real.rpow_mul (by linarith) (1 / 3) 2)]
    rw [show ((6 : ℝ) ^ ((1 : ℝ) / 3)) ^ 5 = ((6 : ℝ) ^ ((1 : ℝ) / 3)) ^ (5 : ℝ) by norm_cast]
    rw [Eq.symm (Real.rpow_mul (by linarith) (1 / 3) 5)]
    ring_nf
    rw [show (5 : ℝ) / 3 = 1 + 2 / 3 by ring]
    rw [Real.rpow_add (by linarith) 1 (2 / 3)]
    simp
    constructor
    .
      linarith
    .
      positivity
  .
    simp [lowerBounds]
    intro a x y z h hx hy hz
    subst a
    rw [show (3 : ℝ)⁻¹ = 1 / 3 by ring]
    rw [show x⁻¹ = 1 / x by field_simp]

    -- Key inequality: For positive real numbers, x^3 + y^3 + z^3 - 3xyz ≥ 0
    have h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 ≥ 0:= by
        intro x y z hx hy hz
        -- This can be proven using the fact that it equals (x+y+z)((x-y)^2 + (y-z)^2 + (z-x)^2)/2
        have h1 : x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 = 1 / 2 * (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) := by ring_nf
        rw [h1]
        positivity

    -- Transform the inequality using cube roots
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

    -- Apply the inequality to three carefully chosen triplets
    have h2:= h1 (x * y) (1 / 3 * (1 / x)) (1 / 2 * (1 / y)) (by positivity) (by positivity) (by positivity)
    have h3:= h1 (y * z) (3 / 2 * (1 / y)) (3 * (1 / z)) (by positivity) (by positivity) (by positivity)
    have h4:= h1 (z * x) (2 / 3 * (1 / x)) (2 * (1 / z)) (by positivity) (by positivity) (by positivity)

    -- Simplify the products in each triplet
    rw [show x * y * (1 / 3 * (1 / x)) * (1 / 2 * (1 / y)) = 1 / 6 by field_simp ; linarith] at h2
    rw [show y * z * (3 / 2 * (1 / y)) * (3 * (1 / z)) = 9 / 2 by field_simp ; linarith] at h3
    rw [show z * x * (2 / 3 * (1 / x)) * (2 * (1 / z)) = 4 / 3 by field_simp ; linarith] at h4

    -- Key equality that helps establish the minimum
    have h5 : ((1 : ℝ) / 6) ^ ((1 : ℝ) / 3) + ((9 : ℝ) / 2) ^ ((1 : ℝ) / 3) + ((4 : ℝ) / 3) ^ ((1 : ℝ) / 3) = (36 ^ ((1 : ℝ) / 3)):= by
      have g1 : 6 * ((1 : ℝ) / 6) ^ ((1 : ℝ) / 3) = 36 ^ ((1 : ℝ) / 3):= by
        rw [show (1 : ℝ) / 6 = 6 ^ ((-1 : ℝ)) by ring]
        rw [Eq.symm (Real.rpow_mul (by linarith) (-1) (1 / 3))]
        rw [show (6 : ℝ) * 6 ^ ((-1) * ((1 : ℝ) / 3)) = 6 ^ (1 : ℝ) * 6 ^ ((-1) * ((1 : ℝ) / 3)) by simp]
        rw [Eq.symm (Real.rpow_add (by linarith) 1 (-1 * (1 / 3)))]
        rw [show (36 : ℝ) = 6 ^ 2 by ring]
        rw [show (6 : ℝ) ^ 2 = 6 ^ (2 : ℝ) by norm_cast]
        rw [Eq.symm (Real.rpow_mul (by linarith) 2 (1 / 3))]
        ring_nf
      have g2 : 2 * ((9 : ℝ) / 2) ^ ((1 : ℝ) / 3) = 36 ^ ((1 : ℝ) / 3):= by
        rw [show (9 : ℝ) / 2 = 36 * 8 ^ (-1 : ℝ) by ring]
        rw [Real.mul_rpow (by positivity) (by positivity)]
        rw [show (8 : ℝ) = 2 ^ 3 by ring]
        rw [show (2 : ℝ) ^ 3 = 2 ^ (3 : ℝ) by norm_cast]
        rw [Eq.symm (Real.rpow_mul (by linarith) 3 (-1))]
        rw [Eq.symm (Real.rpow_mul (by linarith) (3 * -1) (1 / 3))]
        ring_nf
      have g3 : 3 * ((4 : ℝ) / 3) ^ ((1 : ℝ) / 3) = 36 ^ ((1 : ℝ) / 3):= by
        rw [show (4 : ℝ) / 3 = 36 * 27 ^ (-1 : ℝ) by ring]
        rw [Real.mul_rpow (by positivity) (by positivity)]
        rw [show (27 : ℝ) = 3 ^ 3 by ring]
        rw [show (3 : ℝ) ^ 3 = 3 ^ (3 : ℝ) by norm_cast]
        rw [Eq.symm (Real.rpow_mul (by linarith) 3 (-1))]
        rw [Eq.symm (Real.rpow_mul (by linarith) (3 * -1) (1 / 3))]
        ring_nf
      linarith

    -- Complete the proof by combining all inequalities
    rw [show 2 / y = 2 * (1 / y) by field_simp]
    rw [show 5 / z = 5 * (1 / z) by field_simp]
    linarith
