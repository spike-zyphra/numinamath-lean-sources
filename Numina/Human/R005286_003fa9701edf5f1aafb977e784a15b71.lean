import Mathlib
/- Soient $x, y, z$ des réels strictement positifs tels que

$$
x+\frac{y}{z}=y+\frac{z}{x}=z+\frac{x}{y}=2
$$

Déterminer toutes les valeurs possibles que peut prendre le nombre $x+y+z$. -/
theorem algebra_607410 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hxy : x + y / z = 2) (hyz : y + z / x = 2) (hzx : z + x / y = 2) : x + y + z = 3:= by

    -- Helper lemma: For positive reals satisfying the equations, 1 - x ≥ 0
    have h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x + y / z = 2 → y + z / x = 2 → z + x / y = 2 → 1 - x ≥ 0:= by
        intro x y z hx hy hz hxy _ hzx
        -- Inner lemma: For positive reals a and b, a + b ≥ 2√(ab) (AM-GM inequality)
        have h1 : ∀ a b : ℝ, a > 0 → b > 0 → a + b ≥ 2 * √(a * b):= by
            intro a b ha hb
            field_simp
            have g1 : (√a - √b) ^ 2 ≥ 0:= by positivity
            ring_nf at g1
            rw [show √a ^ 2 = a by refine Real.sq_sqrt (by positivity)] at g1
            rw [show √b ^ 2 = b by refine Real.sq_sqrt (by positivity)] at g1
            linarith

        -- Apply AM-GM inequality to specific terms
        have h2:= h1 x (y / z) (by positivity) (by positivity)
        have h3:= h1 z (x / y) (by positivity) (by positivity)
        rw [hxy] at h2
        rw [hzx] at h3
        replace h2 : √(x * (y / z)) ≤ 1:= by linarith
        replace h3 : √(z * (x / y)) ≤ 1:= by linarith
        replace h1 : √(x * (y / z)) * √(z * (x / y)) ≤ 1 * 1:= by refine mul_le_mul_of_nonneg h2 h3 (by positivity) (by positivity)
        rw [show √(x * (y / z)) * √(z * (x / y)) = √((x * (y / z)) * (z * (x / y))) by field_simp] at h1
        rw [show (x * (y / z)) * (z * (x / y)) = x ^ 2 by field_simp ; linarith] at h1
        rw [show √(x ^ 2) = x by refine Real.sqrt_sq (by positivity)] at h1
        linarith

    -- Apply the helper lemma to all cyclic permutations of x, y, z
    have h2:= h1 x y z hx hy hz hxy hyz hzx
    have h3:= h1 y z x hy hz hx hyz hzx hxy
    have h4:= h1 z x y hz hx hy hzx hxy hyz

    -- Show that x*(1-y) + y*(1-z) + z*(1-x) = 0
    replace h1 : x * (1 - y) + y * (1 - z) + z * (1 - x) = 0:= by
        field_simp at hxy hyz hzx
        linarith

    -- Show each term is non-negative
    have g1 : x * (1 - y) ≥ 0:= by positivity
    have g2 : y * (1 - z) ≥ 0:= by positivity
    have g3 : z * (1 - x) ≥ 0:= by positivity

    -- Since sum is zero and each term is non-negative, each term must be zero
    replace g1 : x * (1 - y) = 0:= by linarith
    replace g2 : y * (1 - z) = 0:= by linarith
    replace g3 : z * (1 - x) = 0:= by linarith

    -- Since x, y, z are non-zero
    replace hx : x ≠ 0:= by positivity
    replace hy : y ≠ 0:= by positivity
    replace hz : z ≠ 0:= by positivity

    -- Therefore x = y = z = 1
    replace g1 : 1 - y = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero hx g1
    replace g2 : 1 - z = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero hy g2
    replace g3 : 1 - x = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero hz g3
    linarith
