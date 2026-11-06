import Mathlib

/- Given three real numbers $x, y$ and $z$ such that $0 \leqslant x \leqslant y \leqslant z$ and $x+y+z=1$. Find the maximum value of the expression

$$
(x-y z)^{2}+(y-z x)^{2}+(z-x y)^{2} .
$$ -/
theorem algebra_604692 : IsGreatest {a : ℝ | (∃ x y z : ℝ, 0 ≤ x ∧ x ≤ y ∧ y ≤ z ∧ x + y + z = 1 ∧ a = (x - y * z) ^ 2 + (y - z * x) ^ 2 + (z - x * y) ^ 2)} 1 := by
    simp [IsGreatest]
    constructor
    . -- First part: Prove that 1 belongs to the set (existence)
        use 0  -- Let x = 0
        simp
        use 0  -- Let y = 0
        simp
        use 1  -- Let z = 1
        simp
    . -- Second part: Prove that 1 is an upper bound
        simp [upperBounds]
        intro a x hx y hy z hz h ha
        subst a
        -- Key algebraic transformation of the expression
        have h1 : (x - y * z) ^ 2 + (y - z * x) ^ 2 + (z - x * y) ^ 2 = (x * y + y * z + z * x - 1) ^ 2 - 8 * (x * y * z):= by
            replace h : x = 1 - y - z := by linarith
            rw [h]
            ring_nf
        rw [h1]
        -- Establish non-negativity conditions
        have hy2 : y ≥ 0 := by linarith
        have hz2 : z ≥ 0 := by linarith
        have h2 : x * y * z ≥ 0:= by positivity
        have h3 : x * y + y * z + z * x ≥ 0:= by positivity
        -- Prove upper bound using quadratic inequality
        have h4 : x * y + y * z + z * x ≤ 1 / 3 * (x + y + z) ^ 2:= by
            have g1 : (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 ≥ 0 := by positivity
            linarith
        rw [h] at h4
        field_simp at h4
        -- Establish bounds for the transformed expression
        have h5 : x * y + y * z + z * x - 1 ≥ -1:= by linarith
        have h6 : x * y + y * z + z * x - 1 ≤ -2 / 3:= by linarith
        have h7 : (x * y + y * z + z * x - 1) ^ 2 ≤ 1:= by nlinarith only [h5, h6]
        linarith
