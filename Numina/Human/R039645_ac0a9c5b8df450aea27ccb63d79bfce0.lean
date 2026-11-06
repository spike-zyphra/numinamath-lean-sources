import Mathlib
set_option maxHeartbeats 400000
/- Prove that, for all real numbers $x, y, z$ :

$$
\frac{x^{2}-y^{2}}{2 x^{2}+1}+\frac{y^{2}-z^{2}}{2 y^{2}+1}+\frac{z^{2}-x^{2}}{2 z^{2}+1} \leq(x+y+z)^{2}
$$

When the equality holds? -/
theorem inequalities_606244 (x y z : ℝ) : (x ^ 2 - y ^ 2) / (2 * x ^ 2 + 1) + (y ^ 2 - z ^ 2) / (2 * y ^ 2 + 1) + (z ^ 2 - x ^ 2) / (2 * z ^ 2 + 1) ≤ (x + y + z) ^ 2 ∧ ((x ^ 2 - y ^ 2) / (2 * x ^ 2 + 1) + (y ^ 2 - z ^ 2) / (2 * y ^ 2 + 1) + (z ^ 2 - x ^ 2) / (2 * z ^ 2 + 1) = (x + y + z) ^ 2 ↔ x = 0 ∧ y = 0 ∧ z = 0):= by
    -- Let a = x² + 1/2, b = y² + 1/2, c = z² + 1/2 for simpler notation
    set a:= x ^ 2 + 1 / 2 with ha
    set b:= y ^ 2 + 1 / 2 with hb
    set c:= z ^ 2 + 1 / 2 with hc
    -- Prove a, b, c are positive
    have hapos : a > 0:= by positivity
    have hbpos : b > 0:= by positivity
    have hcpos : c > 0:= by positivity
    clear_value a b c
    -- Simplify the three fractions in terms of a, b, c
    have h1 : (x ^ 2 - y ^ 2) / (2 * x ^ 2 + 1) = 1 / 2 * (a - b) / a:= by
        rw [ha, hb]
        field_simp
        linarith
    have h2 : (y ^ 2 - z ^ 2) / (2 * y ^ 2 + 1) = 1 / 2 * (b - c) / b:= by
        rw [hb, hc]
        field_simp
        linarith
    have h3 : (z ^ 2 - x ^ 2) / (2 * z ^ 2 + 1) = 1 / 2 * (c - a) / c:= by
        rw [hc, ha]
        field_simp
        linarith
    rw [h1, h2, h3]
    clear h1 h2 h3
    -- Key lemma: For positive x, y, z: x³ + y³ + z³ - 3xyz ≥ 0
    -- Equality holds iff x = y = z
    -- This is a fundamental inequality that will help prove our main theorem
    have h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 ≥ 0 ∧ (x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 = 0 → x = y ∧ y = z) := by
        intro x y z hx hy hz
        -- Express the cubic expression as a product of two factors
        -- One factor is (x + y + z)/2, the other is sum of squared differences
        have h1 : x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 = 1 / 2 * (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) := by ring_nf
        rw [h1]
        constructor
        .   -- First part: prove the inequality
            positivity
        .   -- Second part: prove the equality condition
            intro h
            -- If product is zero and first factor is non-zero, second factor must be zero
            have g1 : 1 / 2 * (x + y + z) ≠ 0:= by positivity
            replace h : ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero g1 h
            -- All squared differences are non-negative
            have g2 : (x - y) ^ 2 ≥ 0:= by positivity
            have g3 : (y - z) ^ 2 ≥ 0:= by positivity
            have g4 : (z - x) ^ 2 ≥ 0:= by positivity
            -- If sum of non-negative terms is zero, each term must be zero
            replace g2 : (x - y) ^ 2 = 0:= by linarith only [g2, g3, g4, h]
            replace g3 : (y - z) ^ 2 = 0:= by linarith only [g2, g3, g4, h]
            -- If square is zero, the number itself is zero
            replace g2 : x - y = 0:= by exact pow_eq_zero g2
            replace g3 : y - z = 0:= by exact pow_eq_zero g3
            constructor
            all_goals
            linarith

    -- Transform the lemma to work with cube roots
    -- This gives us: x + y + z - 3(xyz)^(1/3) ≥ 0
    replace h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x + y + z - (x * y * z) ^ ((1 : ℝ) / 3) * 3 ≥ 0 ∧ (x + y + z - (x * y * z) ^ ((1 : ℝ) / 3) * 3 = 0 → x = y ∧ y = z) := by
        intro x y z hx hy hz
        -- Apply the previous lemma to cube roots of x, y, z
        specialize h1 (x ^ ((1 : ℝ) / 3)) (y ^ ((1 : ℝ) / 3)) (z ^ ((1 : ℝ) / 3)) (by positivity) (by positivity) (by positivity)
        -- Series of rewrites to handle cube roots and powers
        rw [show (x ^ ((1 : ℝ) / 3)) ^ 3 = (x ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) by norm_cast] at h1
        rw [show (y ^ ((1 : ℝ) / 3)) ^ 3 = (y ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) by norm_cast] at h1
        rw [show (z ^ ((1 : ℝ) / 3)) ^ 3 = (z ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) by norm_cast] at h1
        rw [(Eq.symm (Real.rpow_mul (by linarith) (1 / 3) 3))] at h1
        rw [(Eq.symm (Real.rpow_mul (by linarith) (1 / 3) 3))] at h1
        rw [(Eq.symm (Real.rpow_mul (by linarith) (1 / 3) 3))] at h1
        rw [show (1 : ℝ) / 3 * 3 = 1 by ring_nf] at h1
        rw [Eq.symm (Real.mul_rpow (by linarith) (by linarith))] at h1
        rw [Eq.symm (Real.mul_rpow (by positivity) (by linarith))] at h1
        simp at h1
        simp
        constructor
        .
            linarith
        .
            intro h
            replace h1:= h1.2 h
            rcases h1 with ⟨g1, g2⟩
            field_simp at g1 g2
            replace g1 : (x ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) = (y ^ ((1 : ℝ) / 3)) ^ (3 : ℝ):= by rw [g1]
            replace g2 : (y ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) = (z ^ ((1 : ℝ) / 3)) ^ (3 : ℝ):= by rw [g2]
            rw [(Eq.symm (Real.rpow_mul (by linarith) (1 / 3) 3))] at g1 g2
            rw [(Eq.symm (Real.rpow_mul (by linarith) (1 / 3) 3))] at g1 g2
            rw [show (1 : ℝ) / 3 * 3 = 1 by ring_nf] at g1 g2
            simp at g1 g2
            constructor
            all_goals
            linarith
    constructor
    .   -- Prove the main inequality
        have h2 : (x + y + z) ^ 2 ≥ 0:= by positivity
        rw [show 1 / 2 * (a - b) / a + 1 / 2 * (b - c) / b + 1 / 2 * (c - a) / c = 1 / 2 * ((a - b) / a + (b - c) / b + (c - a) / c) by ring]
        suffices (a - b) / a + (b - c) / b + (c - a) / c ≤ 0 by linarith only [h2, this]
        rw [show (a - b) / a = 1 - b / a by field_simp]
        rw [show (b - c) / b = 1 - c / b by field_simp]
        rw [show (c - a) / c = 1 - a / c by field_simp]
        specialize h1 (b / a) (c / b) (a / c) (by positivity) (by positivity) (by positivity)
        rw [show b / a * (c / b) * (a / c) = 1 by field_simp ; ring_nf] at h1
        replace h1:= h1.1
        simp at h1
        linarith
    .   -- Prove the equality condition
        constructor
        .   -- Forward direction: if equality holds, then x = y = z = 0
            intro h
            -- Square of sum is always non-negative
            have h2 : (x + y + z) ^ 2 ≥ 0:= by positivity
            -- Apply the key lemma to the ratios b/a, c/b, a/c
            specialize h1 (b / a) (c / b) (a / c) (by positivity) (by positivity) (by positivity)
            -- Simplify the product of ratios to 1
            rw [show b / a * (c / b) * (a / c) = 1 by field_simp ; ring_nf] at h1
            simp at h1
            rcases h1 with ⟨g1, g2⟩
            -- Rewrite fractions in a more manageable form
            rw [show 1 / 2 * (a - b) / a + 1 / 2 * (b - c) / b + 1 / 2 * (c - a) / c = 1 / 2 * ((a - b) / a + (b - c) / b + (c - a) / c) by ring] at h
            rw [show (a - b) / a = 1 - b / a by field_simp] at h
            rw [show (b - c) / b = 1 - c / b by field_simp] at h
            rw [show (c - a) / c = 1 - a / c by field_simp] at h
            replace g2:= g2 (by linarith)
            rcases g2 with ⟨g2, g3⟩
            -- Establish that the product of ratios equals 1
            have g4 : (b / a) * (c / b) * (a / c) = 1:= by field_simp ; linarith
            -- Prove a = b using a case analysis
            have g5 : a = b:= by
                rw [←g3, ←g2] at g4
                field_simp at g4
                replace g4 : (a ^ 2 + b ^ 2 + (a + b) ^ 2) * (a - b) = 0:= by linarith
                by_cases H : a ^ 2 + b ^ 2 + (a + b) ^ 2 = 0
                .   -- Case 1: If sum of squares is zero, each term must be zero
                    have g5 : a ^ 2 ≥ 0:= by positivity
                    have g6 : b ^ 2 ≥ 0:= by positivity
                    have g7 : (a + b) ^ 2 ≥ 0:= by positivity
                    replace g5 : a ^ 2 = 0:= by linarith
                    replace g6 : b ^ 2 = 0:= by linarith
                    replace g5 : a = 0:= by exact pow_eq_zero g5
                    replace g6 : b = 0:= by exact pow_eq_zero g6
                    rw [g5, g6]
                .   -- Case 2: If sum of squares is non-zero, then a - b must be zero
                    replace H : a ^ 2 + b ^ 2 + (a + b) ^ 2 ≠ 0:= by simp [H]
                    replace g4 : a - b = 0:= eq_zero_of_ne_zero_of_mul_left_eq_zero H g4
                    linarith
            -- Similarly prove b = c using the same approach
            have g6 : b = c:= by
                rw [g2, ←g3] at g4
                field_simp at g4
                replace g4 : (b ^ 2 + c ^ 2 + (b + c) ^ 2) * (b - c) = 0:= by linarith
                by_cases H : b ^ 2 + c ^ 2 + (b + c) ^ 2 = 0
                .
                    have g7 : b ^ 2 ≥ 0:= by positivity
                    have g8 : c ^ 2 ≥ 0:= by positivity
                    have g9 : (b + c) ^ 2 ≥ 0:= by positivity
                    replace g7 : b ^ 2 = 0:= by linarith
                    replace g8 : c ^ 2 = 0:= by linarith
                    replace g7 : b = 0:= by exact pow_eq_zero g7
                    replace g8 : c = 0:= by exact pow_eq_zero g8
                    rw [g7, g8]
                .
                    replace H : b ^ 2 + c ^ 2 + (b + c) ^ 2 ≠ 0:= by simp [H]
                    replace g4 : b - c = 0:= eq_zero_of_ne_zero_of_mul_left_eq_zero H g4
                    linarith
            -- Show that x + y + z = 0
            replace h2 : (x + y + z) ^ 2 = 0:= by linarith
            replace h2 : x + y + z = 0:= by exact pow_eq_zero h2
            -- Clean up unnecessary hypotheses
            clear g1 g2 g3 g4 h hapos hbpos hcpos
            -- Convert equations in a, b, c back to x, y, z
            rw [ha, hb] at g5
            rw [hb, hc] at g6
            clear ha hb hc a b c
            -- Show that squares are equal
            replace g5 : x ^ 2 = y ^ 2:= by linarith
            replace g6 : y ^ 2 = z ^ 2:= by linarith
            -- Substitute y = -x - z and simplify
            rw [show y = -x - z by linarith only [h2]] at g5 g6
            replace g5 : z * (2 * x + z) = 0:= by linarith
            replace g6 : x * (2 * z + x) = 0:= by linarith
            -- Further simplification
            rw [show 2 * x + z = x - y by linarith] at g5
            rw [show 2 * z + x = z - y by linarith] at g6
            -- Apply zero product property
            replace g5 : z = 0 ∨ x - y = 0:= by exact mul_eq_zero.mp g5
            replace g6 : x = 0 ∨ z - y = 0:= by exact mul_eq_zero.mp g6
            -- Case analysis to conclude x = y = z = 0
            rcases g5 with g5 | g5
            all_goals
            rcases g6 with g6 | g6
            all_goals
            refine ⟨?_, ?_, ?_⟩
            all_goals
            linarith
        .   -- Reverse direction: if x = y = z = 0, then equality holds
            intro ⟨g1, g2, g3⟩
            rw [ha, hb, hc]
            subst x y z
            ring_nf
