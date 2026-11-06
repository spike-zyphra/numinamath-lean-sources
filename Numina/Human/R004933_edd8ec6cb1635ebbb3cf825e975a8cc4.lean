import Mathlib
/- MLD

Let $x, y, z$ be real numbers, satisfying the relations

$$
\left\{\begin{array}{l}
x \geq 20 \\
y \geq 40 \\
z \geq 1675 \\
x+y+z=2015
\end{array}\right.
$$

Find the greatest value of the product $P=x \cdot y \cdot z$. -/
theorem algebra_604690 : IsGreatest {P | ∃ x y z : ℝ, x ≥ 20 ∧ y ≥ 40 ∧ z ≥ 1675 ∧ x + y + z = 2015 ∧ P = x * y * z} 48407500:= by
    constructor
    -- Part 1: Prove that this value is achievable with x = 170, y = 170, z = 1675
    .
        use 170
        use 170
        use 1675
        simp
        refine ⟨?_, ?_, ?_⟩
        .
            linarith
        .
            linarith
        .
            norm_num
    -- Part 2: Prove that no greater value is possible
    .
        simp [upperBounds]
        intro a x hx y _ z hz h ha
        subst a
        -- Show that 1675 - y ≥ 0
        have h1 : 1675 - y ≥ 0:= by linarith
        -- Prove inequality: y*z ≤ 1675*(y + z - 1675)
        have h2 : y * z ≤ 1675 * (y + z - 1675):= by
            replace hz : z - 1675 ≥ 0:= by linarith
            have h2 : (1675 - y) * (z - 1675) ≥ 0:= by positivity
            linarith
        -- Apply the inequality to x*(y*z)
        have h3 : x * (y * z) ≤ x * (1675 * (y + z - 1675)):= by
            replace hx : x ≥ 0:= by linarith
            exact mul_le_mul_of_nonneg_left h2 hx
        -- Rearrange terms using ring arithmetic
        rw [show x * (1675 * (y + z - 1675)) = 1675 * (x * (y + z - 1675)) by ring] at h3
        -- Apply quadratic inequality to complete the proof
        have h4 : x * (y + z - 1675) ≤ (x + y + z - 1675) ^ 2 / 4:= by
            have h4 : (y + z - 1675 -x) ^ 2 ≥ 0:= by positivity
            linarith
        rw [h] at h4
        norm_num at h4
        linarith
