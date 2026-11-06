import Mathlib
/- Find all ordered triples $(x, y, z)$ of real numbers satisfying the following system of equations:

$$
\begin{aligned}
x^{3} & =\frac{z}{y}-2 \frac{y}{z} \\
y^{3} & =\frac{x}{z}-2 \frac{z}{x} \\
z^{3} & =\frac{y}{x}-2 \frac{x}{y}
\end{aligned}
$$ -/
theorem algebra_605419 {x y z : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (h1 : x ^ 3 = z / y - 2 * y / z) (h2 : y ^ 3 = x / z - 2 * z / x)
    (h3 : z ^ 3 = y / x - 2 * x / y) :
    (x, y, z) = (1, 1, -1) ∨ (x, y, z) = (1, -1, 1) ∨ (x, y, z) = (-1, 1, 1) ∨ (x, y, z) = (-1, -1, -1) := by
        -- Clear denominators in the equations
        field_simp at h1 h2 h3

        -- Key insight: prove that (x^2 + y^2 + z^2)(xyz + 1) = 0
        have h4 : (x ^ 2 + y ^ 2 + z ^ 2) * (x * y * z + 1) = 0:= by linarith

        -- Since x^2 + y^2 + z^2 > 0 for non-zero reals
        have g1 : x ^ 2 + y ^ 2 + z ^ 2 ≠ 0:= by positivity

        -- Therefore xyz + 1 = 0, or xyz = -1
        replace h4 : x * y * z + 1 = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero g1 h4
        replace h4 : x * y * z = -1:= by linarith

        -- Substitute and simplify the original equations
        replace h1 : x ^ 2 * (x * y * z) = z ^ 2 - 2 * y ^ 2:= by linarith
        replace h2 : y ^ 2 * (x * y * z) = x ^ 2 - 2 * z ^ 2:= by linarith
        replace h3 : z ^ 2 * (x * y * z) = y ^ 2 - 2 * x ^ 2:= by linarith
        rw [h4] at h1 h2 h3
        simp at h1 h2 h3

        -- From these equations, we can deduce x^2 = y^2 = z^2
        have h5 : x ^ 2 = y ^ 2:= by linarith
        have h6 : y ^ 2 = z ^ 2:= by linarith
        clear h1 h2 h3

        -- Since xyz = -1, we can deduce that x, y, z must be ±1
        have h1 : (x * y * z) ^ 2 = 1:= by
            rw [h4]
            simp
        ring_nf at h1

        -- Prove that x = ±1
        have gx : (x - 1) * (x + 1) = 0:= by
            rw [←h6, ←h5] at h1
            replace h1 : (x ^ 4 + 1 + (x ^ 2 + 1) ^ 2) * (x ^ 2 - 1) = 0:= by linarith
            have gx : x ^ 4 + 1 + (x ^ 2 + 1) ^ 2 ≠ 0:= by positivity
            replace h1 : x ^ 2 - 1 = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero gx h1
            linarith

        -- Similarly prove y = ±1
        have gy : (y - 1) * (y + 1) = 0:= by
            rw [←h6, h5] at h1
            replace h1 : (y ^ 4 + 1 + (y ^ 2 + 1) ^ 2) * (y ^ 2 - 1) = 0:= by linarith
            have gy : y ^ 4 + 1 + (y ^ 2 + 1) ^ 2 ≠ 0:= by positivity
            replace _ : y ^ 2 - 1 = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero gy h1
            linarith

        -- And z = ±1
        have gz : (z - 1) * (z + 1) = 0:= by
            rw [h5, h6] at h1
            replace h1 : (z ^ 4 + 1 + (z ^ 2 + 1) ^ 2) * (z ^ 2 - 1) = 0:= by linarith
            have gz : z ^ 4 + 1 + (z ^ 2 + 1) ^ 2 ≠ 0:= by positivity
            replace _ : z ^ 2 - 1 = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero gz h1
            linarith
        clear h1 h5 h6 hx hy hz g1

        -- Case analysis on x = ±1 and y = ±1
        replace gx : x - 1 = 0 ∨ x + 1 = 0:= by exact eq_zero_or_eq_zero_of_mul_eq_zero gx
        replace gy : y - 1 = 0 ∨ y + 1 = 0:= by exact eq_zero_or_eq_zero_of_mul_eq_zero gy

        -- Consider all cases and use xyz = -1 to determine z
        rcases gx with gx | gx
        .
            rcases gy with gy | gy
            .
                replace gx : x = 1:= by linarith
                replace gy : y = 1:= by linarith
                subst x y
                simp at h4
                subst z
                simp
            .
                replace gx : x = 1:= by linarith
                replace gy : y = -1:= by linarith
                subst x y
                simp at h4
                subst z
                simp
        .
            rcases gy with gy | gy
            .
                replace gx : x = -1:= by linarith
                replace gy : y = 1:= by linarith
                subst x y
                simp at h4
                subst z
                simp
            .
                replace gx : x = -1:= by linarith
                replace gy : y = -1:= by linarith
                subst x y
                simp at h4
                subst z
                simp
