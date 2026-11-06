import Mathlib

/- For two strictly positive real numbers x and y, prove that:

$$
\left(x+\frac{2}{y}\right)\left(\frac{y}{x}+2\right) \geqslant 8
$$

When does equality hold? -/
theorem algebra_607354 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (x + 2 / y) * (y / x + 2) ≥ 8 ∧ ((x + 2 / y) * (y / x + 2) = 8 ↔ (x = 1 ∧ y = 2)):= by
    -- First, prove a helper lemma about AM-GM inequality:
    -- For positive reals x,y: x + y ≥ 2√(xy) with equality iff x = y
    have h : ∀ x y : ℝ, x > 0 → y > 0 → (x + y ≥ 2 * √(x * y) ∧ (x + y = 2 * √(x * y) → x = y)):= by
        intro x y hx hy
        constructor
        . -- Prove the inequality part using (√x - √y)² ≥ 0
            have h1 : (√x - √y) ^ 2 ≥ 0:= by positivity
            ring_nf at h1
            rw [show √x ^ 2 = x by refine Real.sq_sqrt (by linarith)] at h1
            rw [show √y ^ 2 = y by refine Real.sq_sqrt (by linarith)] at h1
            rw [show √x * √y = √(x * y) by refine Eq.symm (Real.sqrt_mul' x (by linarith))] at h1
            linarith
        . -- Prove the equality case: if x + y = 2√(xy) then x = y
            intro h
            replace h : (√x - √y) ^ 2 = 0:= by
                ring_nf
                rw [show √x ^ 2 = x by refine Real.sq_sqrt (by linarith)]
                rw [show √y ^ 2 = y by refine Real.sq_sqrt (by linarith)]
                rw [show √x * √y = √(x * y) by refine Eq.symm (Real.sqrt_mul' x (by linarith))]
                linarith
            replace h : √x - √y = 0:= by exact pow_eq_zero h
            replace h : √x = √y:= by linarith
            replace h : √x ^ 2 = √y ^ 2:= by rw [h]
            rw [show √x ^ 2 = x by refine Real.sq_sqrt (by linarith)] at h
            rw [show √y ^ 2 = y by refine Real.sq_sqrt (by linarith)] at h
            exact h

    -- Apply AM-GM to x + 2/y
    have h1:= h x (2 / y) hx (by positivity)
    rcases h1 with ⟨h1, h1eq⟩
    -- Apply AM-GM to y/x + 2
    have h2:= h (y / x) 2 (by positivity) (by positivity)
    rcases h2 with ⟨h2, h2eq⟩

    -- Use these inequalities to show the product is ≥ 8
    have h3 : (x + 2 / y) * (y / x + 2) ≥ (2 * √(x * (2 / y))) * (2 * √(y / x * 2)):= mul_le_mul_of_nonneg h1 h2 (by positivity) (by positivity)
    -- Show that the RHS equals 8
    have h4 : (2 * √(x * (2 / y))) * (2 * √(y / x * 2)) = 8:= by
        rw [show (2 * √(x * (2 / y))) * (2 * √(y / x * 2)) = 4 * (√(x * (2 / y)) * √(y / x * 2)) by ring_nf]
        rw [Eq.symm (Real.sqrt_mul' _ (by positivity))]
        rw [show x * (2 / y) * (y / x * 2) = 4 by field_simp ; linarith]
        rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by ring_nf]
        rw [show √((2 : ℝ) ^ 2) = (2 : ℝ) by refine Real.sqrt_sq (by linarith)]
        linarith

    constructor
    . -- Prove the inequality part
        linarith
    . -- Prove the equality case: equality holds iff x = 1 and y = 2
        constructor
        . -- Forward direction: if product = 8, then x = 1 and y = 2
            intro hgoal
            replace h3 : (x + 2 / y) * (y / x + 2) = 2 * √(x * (2 / y)) * (2 * √(y / x * 2)):= by linarith
            clear h4 hgoal
            -- Show that both AM-GM inequalities must be equalities
            replace h1 : x + 2 / y = 2 * √(x * (2 / y)):= by
                have h4 : x + 2 / y ≤ 2 * √(x * (2 / y)):= by
                    by_contra H
                    replace H : x + 2 / y > 2 * √(x * (2 / y)):= by linarith
                    replace H : (x + 2 / y) * (y / x + 2) > 2 * √(x * (2 / y)) * (2 * √(y / x * 2)):= by refine mul_lt_mul_of_pos_of_nonneg' H h2 (by positivity) (by positivity)
                    linarith
                linarith
            rw [←h1] at h3
            replace h2 : y / x + 2 = 2 * √(y / x * 2):= by
                have h4 : y / x + 2 ≤ 2 * √(y / x * 2):= by
                    by_contra H
                    replace H : y / x + 2 > 2 * √(y / x * 2):= by linarith
                    replace H : (x + 2 / y) * (y / x + 2) > (x + 2 / y) * (2 * √(y / x * 2)):= (mul_lt_mul_left (by positivity)).mpr H
                    linarith
                linarith
            -- Use the equality cases of AM-GM to deduce x = 1 and y = 2
            replace h1eq:= h1eq h1
            replace h2eq:= h2eq h2
            clear h1 h2 h3 h
            rw [h1eq] at h2eq
            field_simp at h2eq
            replace h2eq : (y + 2) * (y - 2) = 0:= by linarith
            have h1 : y + 2 ≠ 0:= by
                by_contra H
                linarith
            replace h2eq : y - 2 = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero h1 h2eq
            replace h2eq : y = 2:= by linarith
            rw [h2eq] at h1eq
            simp at h1eq
            exact ⟨h1eq, h2eq⟩
        . -- Backward direction: if x = 1 and y = 2, then product = 8
            intro ⟨g1, g2⟩
            subst x y
            linarith
