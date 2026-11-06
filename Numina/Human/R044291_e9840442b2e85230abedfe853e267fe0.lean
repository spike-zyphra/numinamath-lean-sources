import Mathlib
set_option maxHeartbeats 400000
/- Let $x, y, z$ be positive real numbers such that $x+y+z=\frac{1}{x}+\frac{1}{y}+\frac{1}{z}$.

a) Prove the inequality

$$
x+y+z \geq \sqrt{\frac{x y+1}{2}}+\sqrt{\frac{y z+1}{2}}+\sqrt{\frac{z x+1}{2}}
$$

b) (Added by the problem selecting committee) When does the equality hold? -/
theorem algebra_605196 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 1 / x + 1 / y + 1 / z) :
x + y + z ≥ √((x * y + 1) / 2) + √((y * z + 1) / 2) + √((z * x + 1) / 2) ∧ (x + y + z = √((x * y + 1) / 2) + √((y * z + 1) / 2) + √((z * x + 1) / 2) ↔ x = 1 ∧ y = 1 ∧ z = 1):= by

    -- Helper lemma: Cauchy-Schwarz inequality in 3D and its equality condition
    have h1 : ∀ x1 y1 z1 x2 y2 z2 : ℝ, x1 > 0 → y1 > 0 → z1 > 0 → x2 > 0 → y2 > 0 → z2 > 0 →
        (x1 ^ 2 + y1 ^ 2 + z1 ^ 2) * (x2 ^ 2 + y2 ^ 2 + z2 ^ 2) ≥ (x1 * x2 + y1 * y2 + z1 * z2) ^ 2 ∧ ((x1 ^ 2 + y1 ^ 2 + z1 ^ 2) * (x2 ^ 2 + y2 ^ 2 + z2 ^ 2) = (x1 * x2 + y1 * y2 + z1 * z2) ^ 2 → (x1 / x2 = y1 / y2 ∧ y1 / y2 = z1 / z2)):= by
        intro x1 y1 z1 x2 y2 z2 _ _ _ _ _ _
        have h1 : (x1 * y2 - y1 * x2) ^ 2 + (y1 * z2 - z1 * y2) ^ 2 + (z1 * x2 - x1 * z2) ^ 2 ≥ 0:= by positivity
        constructor
        .
            linarith
        .
            intro h
            have g1 : (x1 * y2 - y1 * x2) ^ 2 ≥ 0:= by positivity
            have g2 : (y1 * z2 - z1 * y2) ^ 2 ≥ 0:= by positivity
            have g3 : (z1 * x2 - x1 * z2) ^ 2 ≥ 0:= by positivity
            replace g1 : (x1 * y2 - y1 * x2) ^ 2 = 0:= by linarith
            replace g2 : (y1 * z2 - z1 * y2) ^ 2 = 0:= by linarith
            replace g3 : (z1 * x2 - x1 * z2) ^ 2 = 0:= by linarith
            simp at g1 g2 g3
            constructor
            all_goals
                field_simp
                linarith
    have h2 : (x * y + 1) / (2 * x) + (y * z + 1) / (2 * y) + (z * x + 1) / (2 * z) = x + y + z:= by
        rw [show (x * y + 1) / (2 * x) = 1 / 2 * y + 1 / 2 * (1 / x) by field_simp ; linarith]
        rw [show (y * z + 1) / (2 * y) = 1 / 2 * z + 1 / 2 * (1 / y) by field_simp ; linarith]
        rw [show (z * x + 1) / (2 * z) = 1 / 2 * x + 1 / 2 * (1 / z) by field_simp ; linarith]
        linarith
    constructor
    .
        -- Part a: Proving the inequality using Cauchy-Schwarz
        rw [show x + y + z = |x + y + z| by exact Eq.symm (abs_of_nonneg (by positivity))]
        rw [show √((x * y + 1) / 2) + √((y * z + 1) / 2) + √((z * x + 1) / 2) = |√((x * y + 1) / 2) + √((y * z + 1) / 2) + √((z * x + 1) / 2)| by exact Eq.symm (abs_of_nonneg (by positivity))]
        suffices (x + y + z) ^ 2 ≥ (√((x * y + 1) / 2) + √((y * z + 1) / 2) + √((z * x + 1) / 2)) ^ 2 by exact sq_le_sq.mp this
        rw [show (x + y + z) ^ 2 = ((x * y + 1) / (2 * x) + (y * z + 1) / (2 * y) + (z * x + 1) / (2 * z)) * (x + y + z) by rw [h2] ; ring_nf]
        specialize h1 √((x * y + 1) / (2 * x)) √((y * z + 1) / (2 * y)) √((z * x + 1) / (2 * z)) √x √y √z (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
        replace h1:= h1.1
        rw [Real.sq_sqrt (by positivity)] at h1
        rw [Real.sq_sqrt (by positivity)] at h1
        rw [Real.sq_sqrt (by positivity)] at h1
        rw [Real.sq_sqrt (by positivity)] at h1
        rw [Real.sq_sqrt (by positivity)] at h1
        rw [Real.sq_sqrt (by positivity)] at h1
        rw [show √((x * y + 1) / (2 * x)) * √x = √((x * y + 1) / (2 * x) * x) by field_simp] at h1
        rw [show √((y * z + 1) / (2 * y)) * √y = √((y * z + 1) / (2 * y) * y) by field_simp] at h1
        rw [show √((z * x + 1) / (2 * z)) * √z = √((z * x + 1) / (2 * z) * z) by field_simp] at h1
        rw [show (x * y + 1) / (2 * x) * x = (x * y + 1) / 2 by field_simp ; linarith] at h1
        rw [show (y * z + 1) / (2 * y) * y = (y * z + 1) / 2 by field_simp ; linarith] at h1
        rw [show (z * x + 1) / (2 * z) * z = (z * x + 1) / 2 by field_simp ; linarith] at h1
        exact h1
    .
        -- Part b: Proving the equality conditions (x = y = z = 1)
        constructor
        .
            -- Forward direction: equality implies x = y = z = 1
            intro hgoal
            replace hgoal : (x + y + z) ^ 2 = (√((x * y + 1) / 2) + √((y * z + 1) / 2) + √((z * x + 1) / 2)) ^ 2:= by rw [hgoal]
            rw [show (x + y + z) ^ 2 = ((x * y + 1) / (2 * x) + (y * z + 1) / (2 * y) + (z * x + 1) / (2 * z)) * (x + y + z) by rw [h2] ; ring_nf] at hgoal
            specialize h1 √((x * y + 1) / (2 * x)) √((y * z + 1) / (2 * y)) √((z * x + 1) / (2 * z)) √x √y √z (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
            replace h1:= h1.2
            -- refine the terms
            rw [Real.sq_sqrt (by positivity)] at h1
            rw [Real.sq_sqrt (by positivity)] at h1
            rw [Real.sq_sqrt (by positivity)] at h1
            rw [Real.sq_sqrt (by positivity)] at h1
            rw [Real.sq_sqrt (by positivity)] at h1
            rw [Real.sq_sqrt (by positivity)] at h1
            rw [show √((x * y + 1) / (2 * x)) * √x = √((x * y + 1) / (2 * x) * x) by field_simp] at h1
            rw [show √((y * z + 1) / (2 * y)) * √y = √((y * z + 1) / (2 * y) * y) by field_simp] at h1
            rw [show √((z * x + 1) / (2 * z)) * √z = √((z * x + 1) / (2 * z) * z) by field_simp] at h1
            rw [show (x * y + 1) / (2 * x) * x = (x * y + 1) / 2 by field_simp ; linarith] at h1
            rw [show (y * z + 1) / (2 * y) * y = (y * z + 1) / 2 by field_simp ; linarith] at h1
            rw [show (z * x + 1) / (2 * z) * z = (z * x + 1) / 2 by field_simp ; linarith] at h1
            replace h1:= h1 hgoal
            rcases h1 with ⟨g1, g2⟩
            replace g1 : (√((x * y + 1) / (2 * x)) / √x) ^ 2 = (√((y * z + 1) / (2 * y)) / √y) ^ 2:= by rw [g1]
            replace g2 : (√((y * z + 1) / (2 * y)) / √y) ^ 2 = (√((z * x + 1) / (2 * z)) / √z) ^ 2:= by rw [g2]
            rw [show (√((x * y + 1) / (2 * x)) / √x) ^ 2 = √((x * y + 1) / (2 * x)) ^ 2 / √x ^ 2 by ring] at g1
            rw [show (√((y * z + 1) / (2 * y)) / √y) ^ 2 = √((y * z + 1) / (2 * y)) ^ 2 / √y ^ 2 by ring] at g2
            rw [show (√((y * z + 1) / (2 * y)) / √y) ^ 2 = √((y * z + 1) / (2 * y)) ^ 2 / √y ^ 2 by ring] at g1
            rw [show (√((z * x + 1) / (2 * z)) / √z) ^ 2 = √((z * x + 1) / (2 * z)) ^ 2 / √z ^ 2 by ring] at g2
            rw [Real.sq_sqrt (by positivity)] at g1 g2
            rw [Real.sq_sqrt (by positivity)] at g1 g2
            rw [Real.sq_sqrt (by positivity)] at g1 g2
            rw [Real.sq_sqrt (by positivity)] at g1 g2
            rw [show (x * y + 1) / (2 * x) / x = 1 / 2 * ((y + 1 / x) / x) by field_simp ; linarith] at g1
            rw [show (y * z + 1) / (2 * y) / y = 1 / 2 * ((z + 1 / y) / y) by field_simp ; linarith] at g2
            rw [show (y * z + 1) / (2 * y) / y = 1 / 2 * ((z + 1 / y) / y) by field_simp ; linarith] at g1
            rw [show (z * x + 1) / (2 * z) / z = 1 / 2 * ((x + 1 / z) / z) by field_simp ; linarith] at g2
            replace g1 : (y + 1 / x) / x = (z + 1 / y) / y:= by linarith
            replace g2 : (z + 1 / y) / y = (x + 1 / z) / z:= by linarith
            set t:= (y + 1 / x) / x with ht
            rw [←g1] at g2
            clear_value t
            -- get the equality condition
            replace ht : x * t = y + 1 / x:= by rw [ht] ; field_simp ; linarith
            replace g1 : y * t = z + 1 / y:= by rw [g1] ; field_simp ; linarith
            replace g2 : z * t = x + 1 / z:= by rw [g2] ; field_simp ; linarith
            have g3 : (x + y + z) * t = (x + y + z) + (1 / x + 1 / y + 1 / z):= by linarith
            rw [←h] at g3
            replace g3 : (x + y + z) * (t - 2) = 0:= by linarith
            have g4 : x + y + z ≠ 0:= by linarith
            simp [g4] at g3
            replace g3 : t = 2:= by linarith
            subst t
            clear g4
            clear h h2 hgoal
            have g3 : x = y:= by
                by_contra H
                replace H : x < y ∨ y < x:= by exact lt_or_gt_of_ne H
                rcases H with H | H
                .
                    have g3 : 1 / x > 1 / y:= by exact (one_div_lt_one_div hy hx).mpr H
                    replace g3 : y < z:= by linarith
                    have g4 : 1 / y > 1 / z:= by exact (one_div_lt_one_div hz hy).mpr g3
                    replace g4 : z < x:= by linarith
                    linarith
                .
                    have g3 : 1 / y > 1 / x:= by exact (one_div_lt_one_div hx hy).mpr H
                    replace g3 : z < y:= by linarith
                    have g4 : z < x:= by linarith
                    replace g4 : 1 / z > 1 / x:= by exact (one_div_lt_one_div hx hz).mpr g4
                    replace g4 : x < z:= by linarith
                    linarith
            subst x
            field_simp at ht
            replace ht : (y + 1) * (y - 1) = 0:= by linarith
            have g3 : y + 1 ≠ 0:= by linarith
            simp [g3] at ht
            replace ht : y = 1:= by linarith
            subst y
            simp at g1
            replace g1 : z = 1:= by linarith
            subst z
            simp
        .
            -- Reverse direction: x = y = z = 1 implies equality
            intro hgoal
            clear h1 h2
            rcases hgoal with ⟨g1, g2, g3⟩
            subst x y z
            ring_nf
            simp
