import Mathlib
/- Real numbers $x, y, z$ satisfy
$$
0< x, y, z<1
$$

and

$$
x y z=(1-x)(1-y)(1-z) .
$$

Show that

$$
\frac{1}{4} \leq \max \{(1-x) y,(1-y) z,(1-z) x\}
$$ -/
theorem algebra_605121 (x y z : ℝ) (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1) (hz : 0 < z ∧ z < 1) (h : x * y * z = (1 - x) * (1 - y) * (1 - z)) :
    max ((1 - x) * y) (max ((1 - y) * z) ((1 - z) * x)) ≥ 1 / 4 := by
        -- Unpack the bounds for x, y, z
        rcases hx with ⟨hx1, hx2⟩
        rcases hy with ⟨hy1, hy2⟩
        rcases hz with ⟨hz1, hz2⟩
        -- Proof by contradiction
        by_contra H
        simp at H
        field_simp at H
        -- H1, H2, H3 represent that all three terms are less than 1/4
        rcases H with ⟨H1, H2, H3⟩
        -- Case analysis: either x ≤ 1/2 or x > 1/2
        by_cases h1 : x ≤ 1 / 2
        . -- Case 1: x ≤ 1/2
            -- If x ≤ 1/2, then 1-x ≥ 1/2
            have h2 : 1 - x ≥ 1 / 2:= by linarith
            -- This implies (1-x)y ≥ (1/2)y
            replace h2 : (1 - x) * y ≥ (1 / 2) * y:= by exact (mul_le_mul_iff_of_pos_right hy1).mpr h2
            -- Since (1-x)y < 1/4, y must be < 1/2
            replace h2 : y < 1 / 2:= by linarith
            -- Similar reasoning for z
            have h3 : 1 - y ≥ 1 / 2:= by linarith
            replace h3 : (1 - y) * z ≥ (1 / 2) * z:= by exact (mul_le_mul_iff_of_pos_right hz1).mpr h3
            replace h3 : z < 1 / 2:= by linarith
            -- Sub-case: x = 1/2 or x < 1/2
            by_cases h4 : x = 1 / 2
            . -- Sub-case 1: x = 1/2
                -- Derive contradiction using the original equation
                subst x
                replace _ : y * z = (1 - y) * (1 - z):= by linarith
                have _ : y * z < (1 / 2) * (1 / 2):= by exact mul_lt_mul_of_pos' h2 h3 hz1 hx1
                replace h2 : 1 - y > 1 / 2:= by linarith
                replace _ : 1 - z > 1 / 2:= by linarith
                have _ : (1 - y) * (1 - z) > (1 / 2) * (1 / 2):= by refine mul_lt_mul_of_pos_of_nonneg' h2 (by linarith) hx1 (by linarith)
                linarith
            . -- Sub-case 2: x < 1/2
                -- Similar contradiction using the original equation
                replace h1 : x < 1 / 2:= by
                    by_contra!
                    replace this : x = 1 / 2:= by linarith
                    trivial
                clear h4
                -- Show xyz < 1/8
                have g1 : x * y < (1 / 2) * (1 / 2):= by exact mul_lt_mul_of_pos' h1 h2 hy1 (by linarith)
                replace g1 : x * y * z < (1 / 2) * (1 / 2) * (1 / 2):= by exact mul_lt_mul_of_pos' g1 h3 hz1 (by linarith)
                -- Show (1-x)(1-y)(1-z) > 1/8
                replace h1 : 1 - x > 1 / 2:= by linarith
                replace _ : 1 - y > 1 / 2:= by linarith
                replace h3 : 1 - z > 1 / 2:= by linarith
                have g2 : (1 - x) * (1 - y) > (1 / 2) * (1 / 2):= by refine mul_lt_mul_of_pos_of_nonneg' h1 (by linarith) (by linarith) (by linarith)
                replace _ : (1 - x) * (1 - y) * (1 - z) > (1 / 2) * (1 / 2) * (1 / 2):= by exact mul_lt_mul_of_pos' g2 h3 (by linarith) (by linarith)
                linarith
        . -- Case 2: x > 1/2
            -- Similar reasoning as Case 1, but with opposite inequalities
            simp at h1
            field_simp at h1
            have h2 : (1 - z) * x > (1 - z) * (1 / 2):= by refine (mul_lt_mul_left (by linarith)).mpr h1
            replace h2 : z > 1 / 2:= by linarith
            have h3 : (1 - y) * z > (1 - y) * (1 / 2):= by refine (mul_lt_mul_left (by linarith)).mpr h2
            replace h3 : y > 1 / 2:= by linarith
            -- Show xyz > 1/8
            have g1 : x * y > (1 / 2) * (1 / 2):= by exact mul_lt_mul_of_pos' h1 h3 (by linarith) (by linarith)
            replace _ : x * y * z > (1 / 2) * (1 / 2) * (1 / 2):= by exact mul_lt_mul_of_pos' g1 h2 (by linarith) (by linarith)
            -- Show (1-x)(1-y)(1-z) < 1/8
            replace h1 : 1 - x < 1 / 2:= by linarith
            replace h3 : 1 - y < 1 / 2:= by linarith
            replace h2 : 1 - z < 1 / 2:= by linarith
            have g2 : (1 - x) * (1 - y) < (1 / 2) * (1 / 2):= by refine mul_lt_mul_of_pos_of_nonneg' h1 (by linarith) (by linarith) (by linarith)
            replace g2 : (1 - x) * (1 - y) * (1 - z) < (1 / 2) * (1 / 2) * (1 / 2):= by exact mul_lt_mul_of_pos' g2 h2 (by linarith) (by linarith)
            linarith
