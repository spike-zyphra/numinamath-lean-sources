import Mathlib
/- Let $a \circ b=a+b-a b$. Find all triples $(x, y, z)$ of integers such that $(x \circ y) \circ z+(y \circ z) \circ x+(z \circ x) \circ y=0$. -/
theorem algebra_606366 (f : ℤ × ℤ → ℤ) (h : ∀ a b : ℤ, f (a, b) = a + b - a * b) :
{(x, y, z) : ℤ × ℤ × ℤ | f (f (x, y), z) + f (f (y, z), x) + f (f (z, x), y) = 0} =
{(0, 0, 0), (0, 2, 2), (2, 0, 2), (2, 2, 0)}:= by

    -- Extend to consider all possible triples (x,y,z)
    ext ⟨x, y, z⟩
    constructor
    .
        -- Forward direction: prove that if the equation holds, (x,y,z) must be one of the four solutions
        intro h1
        simp [h] at h1
        -- Simplify the equation to 3*((x-1)*(y-1)*(z-1) + 1) = 0
        replace h1 : 3 * ((x - 1) * (y - 1) * (z - 1) + 1) = 0:= by linarith
        -- Further simplify to (x-1)*(y-1)*(z-1) = -1
        replace h1 : (x - 1) * (y - 1) * (z - 1) = -1:= by omega

        -- Prove that absolute values of factors multiply to 1
        have h2 : |x - 1| * |y - 1| * |z - 1| = 1:= by
            replace h1 : |(x - 1) * (y - 1) * (z - 1)| = |-1|:= by rw [h1]
            norm_num at h1
            rw [abs_mul ((x - 1) * (y - 1)) (z - 1)] at h1
            rw [abs_mul (x - 1) (y - 1)] at h1
            exact h1

        -- Prove that none of the factors can be zero
        have h3 : |x - 1| ≠ 0 ∧ |y - 1| ≠ 0 ∧ |z - 1| ≠ 0:= by
            refine ⟨?_, ?_, ?_⟩
            all_goals
                by_contra H
                rw [H] at h2
                simp at h2
        rcases h3 with ⟨h3x, h3y, h3z⟩
        simp at h3x h3y h3z

        -- Prove that absolute values of factors are at least 1
        replace h3x : |x - 1| ≥ 1:= by exact abs_pos.mpr h3x
        replace h3y : |y - 1| ≥ 1:= by exact abs_pos.mpr h3y
        replace h3z : |z - 1| ≥ 1:= by exact abs_pos.mpr h3z

        -- Prove that absolute values of factors must be less than 2
        have h4 : |x - 1| < 2 ∧ |y - 1| < 2 ∧ |z - 1| < 2:= by
            refine ⟨?_, ?_, ?_⟩
            all_goals
                by_contra H
                simp at H
            .
                replace H : |x - 1| * |y - 1| ≥ 2 * 1:= by refine Int.mul_le_mul H h3y (by omega) (by positivity)
                replace H : |x - 1| * |y - 1| * |z - 1| ≥ 2 * 1 * 1:= by refine Int.mul_le_mul H h3z (by omega) (by positivity)
                linarith
            .
                replace H : |y - 1| * |z - 1| ≥ 2 * 1:= by refine Int.mul_le_mul H h3z (by omega) (by positivity)
                replace H : |y - 1| * |z - 1| * |x - 1| ≥ 2 * 1 * 1:= by refine Int.mul_le_mul H h3x (by omega) (by positivity)
                linarith
            .
                replace H : |z - 1| * |x - 1| ≥ 2 * 1:= by refine Int.mul_le_mul H h3x (by omega) (by positivity)
                replace H : |z - 1| * |x - 1| * |y - 1| ≥ 2 * 1 * 1:= by refine Int.mul_le_mul H h3y (by omega) (by positivity)
                linarith

        -- Since 1 ≤ |x-1|,|y-1|,|z-1| < 2, and their product is 1, they must all equal 1
        rcases h4 with ⟨h4x, h4y, h4z⟩
        replace h3x : |x - 1| = 1:= by omega
        replace h3y : |y - 1| = 1:= by omega
        replace h3z : |z - 1| = 1:= by omega
        clear h4x h4y h4z h2

        -- Use these facts to determine the possible values of x, y, and z
        simp [abs_eq] at h3x h3y h3z
        rcases h3x with h3x1 | h3x2
        .
            rcases h3y with h3y1 | h3y2
            .
                rw [h3x1, h3y1] at h1
                simp at h1
                replace h3x1 : x = 2:= by omega
                replace h3y1 : y = 2:= by omega
                subst x y z
                simp
            .
                replace h3x1 : x = 2:= by omega
                subst x y
                simp at h1
                replace h1 : z = 2:= by omega
                subst z
                simp
        .
            rcases h3y with h3y1 | h3y2
            .
                replace h3y1 : y = 2:= by omega
                subst x y
                simp at h1
                replace h1 : z = 2:= by omega
                subst z
                simp
            .
                subst x y
                simp at h1
                subst z
                simp
    .
        -- Backward direction: prove that each of the four solutions satisfies the equation
        intro h1
        simp at h1
        rcases h1 with h1 | h1 | h1 | h1
        all_goals
            rcases h1 with ⟨h1, h2, h3⟩
            subst x y z
            simp [h]
