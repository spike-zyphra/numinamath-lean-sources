import Mathlib
/- Déterminer la valeur maximale de $\sqrt{x}+\sqrt{2 y+2}+\sqrt{3 z+6}$ lorsque $x, y, z$ sont des nombres réels strictement positifs vérifiant $x+y+z=3$. -/
theorem algebra_605450 : IsGreatest {a : ℝ | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x + y + z = 3 ∧ a = √x + √(2 * y + 2) + √(3 * z + 6)} 6:= by
    constructor
    -- First part: Prove that 6 is in the set (achieved when x=y=z=1)
    .
        simp
        use 1
        simp
        use 1
        simp
        use 1
        simp
        constructor
        .
            linarith
        .
            ring_nf
            -- Simplify numerical expressions
            rw [show (4 : ℝ) = 2 ^ 2 by linarith]
            rw [show (9 : ℝ) = 3 ^ 2 by linarith]
            field_simp
            linarith
    -- Second part: Prove that 6 is an upper bound
    .
        simp [upperBounds]
        intro a x hx y hy z hz hsum ha
        subst a
        -- Key inequality: For positive a,b, √(ab) ≤ (a+b)/2 (AM-GM inequality)
        have h1 : ∀ a b : ℝ, a > 0 → b > 0 → √(a * b) ≤ (a + b) / 2:= by
            intro a b ha hb
            field_simp
            have g1 : (√a - √b) ^ 2 ≥ 0:= by positivity
            ring_nf at g1
            rw [show √a ^ 2 = a by refine Real.sq_sqrt (by positivity)] at g1
            rw [show √b ^ 2 = b by refine Real.sq_sqrt (by positivity)] at g1
            linarith
        -- Apply AM-GM inequality to each term
        have h2:= h1 x 1 (by linarith) (by linarith)
        have h3:= h1 (y + 1) 2 (by linarith) (by linarith)
        have h4:= h1 (z + 2) 3 (by linarith) (by linarith)
        ring_nf at h2 h3 h4
        ring_nf
        linarith
