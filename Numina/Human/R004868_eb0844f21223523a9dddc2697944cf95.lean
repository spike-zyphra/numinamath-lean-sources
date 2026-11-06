import Mathlib
/- Let $x, y$ and $z$ be positive real numbers such that $x y+y z+z x=3 x y z$. Prove that

$$
x^{2} y+y^{2} z+z^{2} x \geq 2(x+y+z)-3
$$

and determine when equality holds. -/
theorem inequalities_604335 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y + y * z + z * x = 3 * x * y * z) :
    x ^ 2 * y + y ^ 2 * z + z ^ 2 * x ≥ 2 * (x + y + z) - 3 ∧
    (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x = 2 * (x + y + z) - 3 ↔ x = 1 ∧ y = 1 ∧ z = 1) := by
    -- Transform the condition into sum of reciprocals form: 1/x + 1/y + 1/z = 3
    replace h : 1 / x + 1 / y + 1 / z = 3 := by
        field_simp
        linarith only [h]
    rw [←h]

    -- Prove three key inequalities using perfect square form
    -- First inequality: x²y - 2x + 1/y ≥ 0 by showing it equals (x - 1/y)²y
    have h1 : x ^ 2 * y - 2 * x + 1 / y ≥ 0:= by
        have h1 : x ^ 2 * y - 2 * x + 1 / y = (x - 1 / y) ^ 2 * y:= by
            field_simp
            linarith
        rw [h1]
        positivity

    -- Second inequality: y²z - 2y + 1/z ≥ 0 by showing it equals (y - 1/z)²z
    have h2 : y ^ 2 * z - 2 * y + 1 / z ≥ 0:= by
        have h2 : y ^ 2 * z - 2 * y + 1 / z = (y - 1 / z) ^ 2 * z:= by
            field_simp
            linarith
        rw [h2]
        positivity

    -- Third inequality: z²x - 2z + 1/x ≥ 0 by showing it equals (z - 1/x)²x
    have h3 : z ^ 2 * x - 2 * z + 1 / x ≥ 0:= by
        have h3 : z ^ 2 * x - 2 * z + 1 / x = (z - 1 / x) ^ 2 * x:= by
            field_simp
            linarith
        rw [h3]
        positivity

    constructor
    -- Prove the main inequality using the three inequalities above
    .
        linarith

    -- Prove the equality condition: equality holds if and only if x = y = z = 1
    .
        constructor
        -- Forward direction: if equality holds, then x = y = z = 1
        .
            intro hgoal
            -- Show that all three squared terms must be zero
            replace h1 : x ^ 2 * y - 2 * x + 1 / y = 0:= by linarith
            replace h2 : y ^ 2 * z - 2 * y + 1 / z = 0:= by linarith
            replace h3 : z ^ 2 * x - 2 * z + 1 / x = 0:= by linarith
            -- Rewrite each equation in perfect square form
            rw [show x ^ 2 * y - 2 * x + 1 / y = (x - 1 / y) ^ 2 * y by field_simp ; linarith] at h1
            rw [show y ^ 2 * z - 2 * y + 1 / z = (y - 1 / z) ^ 2 * z by field_simp ; linarith] at h2
            rw [show z ^ 2 * x - 2 * z + 1 / x = (z - 1 / x) ^ 2 * x by field_simp ; linarith] at h3
            -- Deduce that each squared term is zero
            replace h1 : (x - 1 / y) ^ 2 = 0:= by exact eq_zero_of_ne_zero_of_mul_right_eq_zero (by positivity) h1
            replace h2 : (y - 1 / z) ^ 2 = 0:= by exact eq_zero_of_ne_zero_of_mul_right_eq_zero (by positivity) h2
            replace h3 : (z - 1 / x) ^ 2 = 0:= by exact eq_zero_of_ne_zero_of_mul_right_eq_zero (by positivity) h3
            -- Square root of zero is zero
            replace h1 : x - 1 / y = 0:= by exact pow_eq_zero h1
            replace h2 : y - 1 / z = 0:= by exact pow_eq_zero h2
            replace h3 : z - 1 / x = 0:= by exact pow_eq_zero h3
            -- Rearrange to get relationships between x, y, and z
            replace h1 : x = 1 / y:= by linarith
            replace h2 : y = 1 / z:= by linarith
            replace h3 : z = 1 / x:= by linarith
            -- Use these relationships to prove x = y = z = 1
            rw [←h1, ←h2, ←h3] at h
            rw [h2] at h1
            field_simp at h1
            rw [h3] at h2
            field_simp at h2
            refine ⟨?_, ?_, ?_⟩
            all_goals
            linarith
        -- Backward direction: if x = y = z = 1, then equality holds
        .
            intro hgoal
            rcases hgoal with ⟨g1, g2, g3⟩
            subst x y z
            ring_nf
