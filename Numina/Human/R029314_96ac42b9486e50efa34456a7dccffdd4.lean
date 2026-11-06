import Mathlib

/- Task 3. (15 points) Solve the system of equations


$$

\left\{\begin{array}{l}
x^{2}-23 y-25 z=-681 \\
y^{2}-21 x-21 z=-419 \\
z^{2}-19 x-21 y=-313
\end{array}\right.

$$
 -/
theorem algebra_213309 {x y z : ℤ} (h₀ : x^2 - 23 * y - 25 * z = -681) (h₁ : y^2 - 21 * x - 21 * z = -419) (h₂ : z^2 - 19 * x - 21 * y = -313) :
    (x, y, z) = (20, 22, 23) := by

        --Add the three equations and get (x - 20)^2 + (y - 22)^2 + (z - 23)^2 = 0.
        have h1 : (x - 20)^2 + (y - 22)^2 + (z - 23)^2 = 0 := by
            calc
                _ = x^2 - 40 * x + 400 + y^2 - 44 * y + 484 + z^2 - 46 * z + 529 := by ring
                _ = x^2 + y^2 + z^2 - 40 * x - 44 * y - 46 * z + 1413 := by ring
                _ = x^2 - 23 * y - 25 * z + 681 + y^2 - 21 * x - 21 * z + 419 + z^2 - 19 * x - 21 * y + 313 := by linarith
                _ = 0 := by linarith

        --Show (x - 20)^2 + (y - 22)^2 = 0.
        have h2 : (x - 20)^2 + (y - 22)^2 = 0 := by
            have h21 : (x - 20)^2 + (y - 22)^2 = - (z - 23)^2 := by linarith
            have h22 :  - (z - 23)^2 ≤ 0 := by
                refine Int.neg_nonpos_of_nonneg ?_
                exact sq_nonneg (z - 23)
            have h23 : (x - 20)^2 + (y - 22)^2 ≤ 0 := by exact le_of_eq_of_le h21 h22
            have h24 : (x - 20)^2 + (y - 22)^2 ≥ 0 := by
                refine Int.add_nonneg ?_ ?_
                exact sq_nonneg (x - 20)
                exact sq_nonneg (y - 22)
            have h25 : (x - 20)^2 + (y - 22)^2 = 0 := by
                exact Eq.symm (Int.le_antisymm h24 h23)
            exact h25

        -- Show x - 20 = 0 and y - 22 = 0.
        have hx_y : x - 20 = 0 ∧ y - 22 = 0 := by
            have hx_geq_0 : (x - 20)^2 ≥ 0 := by exact sq_nonneg (x - 20)
            have hy_geq_0 : (y - 22)^2 ≥ 0 := by exact sq_nonneg (y - 22)
            have hxy_eq_0 : (x - 20)^2 = 0 ∧ (y - 22)^2 = 0 := by
                exact (add_eq_zero_iff_of_nonneg hx_geq_0 hy_geq_0).mp h2
            constructor
            exact sq_eq_zero_iff.mp hxy_eq_0.1
            exact sq_eq_zero_iff.mp hxy_eq_0.2

        --Show z - 23 = 0.
        have hz_23 : z - 23 = 0 := by
            rw [hx_y.1] at h1
            rw [hx_y.2] at h1
            simp at h1
            exact h1

        --Show x = 20 using x - 20 = 0.
        have hx : x = 20 := by
            have hx_20 : x - 20 = 0 := by exact hx_y.1
            linarith

        --Show y = 22 using y - 22 = 0.
        have hy : y = 22 := by
            have hy_22 : y - 22 = 0 := by exact hx_y.2
            linarith

        --Show z = 23 using z - 23 = 0.
        have hz : z = 23 := by
            linarith

        --Finally show (x, y, z) = (20, 22, 23).
        refine Prod.mk.inj_iff.mpr ?_
        constructor
        exact hx
        exact Prod.ext hy hz