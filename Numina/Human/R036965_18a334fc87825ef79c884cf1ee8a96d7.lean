import Mathlib
/- Let $a, b, c$ be positive real numbers such that $a+b+c=4 \sqrt[ 3]{a b c}$. Prove that  $$ 2(a b+b c+c a)+4 \min \left(a^{2}, b^{2}, c^{2}\right) \geq a^{2}+b^{2}+c^{2} . $$ -/
theorem algebra_605473 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 4 * (a * b * c) ^ ((1 : ℝ) / 3)) :
    2 * (a * b + b * c + c * a) +
    4 * min (min (a ^ 2) (b ^ 2)) (c ^ 2) ≥ a ^ 2 + b ^ 2 + c ^ 2 := by
        -- Main lemma: Proves the inequality when c^2 is the minimum of {a^2, b^2, c^2}
        have h1 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 4 * (a * b * c) ^ ((1 : ℝ) / 3) → min (min (a ^ 2) (b ^ 2)) (c ^ 2) = c ^ 2 → 2 * (a * b + b * c + c * a) + 4 * c ^ 2 ≥ a ^ 2 + b ^ 2 + c ^ 2 := by
            intro a b c ⟨ha, hb, hc, h⟩ h1
            -- Normalize by substituting x = a/c and y = b/c to simplify the problem
            set x:= a / c with hx
            set y:= b / c with hy
            have g1 : a = x * c:= by rw [hx] ; field_simp
            have g2 : b = y * c:= by rw [hy] ; field_simp
            clear_value x y

            -- Substitute and simplify the expressions involving x, y, c
            rw [g1, g2]
            rw [show 2 * (x * c * (y * c) + y * c * c + c * (x * c)) + 4 * c ^ 2 = c ^ 2 * (2 * x * y + 2 * y + 2 * x + 4) by linarith]
            rw [show (x * c) ^ 2 + (y * c) ^ 2 + c ^ 2 = c ^ 2 * (x ^ 2 + y ^ 2 + 1) by ring]

            -- Since c > 0, c^2 > 0, which allows us to divide both sides by c^2
            have g3 : c ^ 2 > 0:= by positivity
            suffices 2 * x * y + 2 * y + 2 * x + 4 ≥ x ^ 2 + y ^ 2 + 1 by exact (mul_le_mul_iff_of_pos_left g3).mpr this

            -- Series of transformations to handle the minimum condition
            rw [g1, g2] at h1
            rw [show (x * c) ^ 2 = c ^ 2 * x ^ 2 by ring] at h1
            rw [show (y * c) ^ 2 = c ^ 2 * y ^ 2 by ring] at h1
            rw [Eq.symm (mul_min_of_nonneg (x ^ 2) (y ^ 2) (by linarith))] at h1
            have g4 : min (c ^ 2 * min (x ^ 2) (y ^ 2)) (c ^ 2) = min (c ^ 2 * min (x ^ 2) (y ^ 2)) (c ^ 2 * 1):= by simp
            rw [g4] at h1

            -- Derive that min(x^2, y^2) ≥ 1
            rw [Eq.symm (mul_min_of_nonneg (min (x ^ 2) (y ^ 2)) 1 (by linarith))] at h1
            replace h1 : c ^ 2 * (min (min (x ^ 2) (y ^ 2)) 1 - 1) = 0:= by linarith
            replace g3 : c ^ 2 ≠ 0:= by positivity
            replace h1 : min (min (x ^ 2) (y ^ 2)) 1 - 1 = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero g3 h1
            replace h1 : min (min (x ^ 2) (y ^ 2)) 1 = 1:= by linarith
            replace h1 : min (x ^ 2) (y ^ 2) ≥ 1:= by exact right_eq_inf.mp (id (Eq.symm h1))

            -- Therefore x^2 ≥ 1 and y^2 ≥ 1
            have gx : x ^ 2 ≥ min (x ^ 2) (y ^ 2):= by exact min_le_left (x ^ 2) (y ^ 2)
            have gy : y ^ 2 ≥ min (x ^ 2) (y ^ 2):= by exact min_le_right (x ^ 2) (y ^ 2)
            have hxpos : x > 0:= by rw [hx] ; positivity
            have hypos : y > 0:= by rw [hy] ; positivity

            -- Simplify the original equation using substitutions
            rw [g1, g2] at h
            rw [show x * c + y * c + c = c * (x + y + 1) by ring] at h
            rw [show x * c * (y * c) * c = x * y * c ^ 3 by ring] at h

            -- Handle the cube root expressions
            rw [show (x * y * c ^ 3) ^ ((1 : ℝ) / 3) = (x * y) ^ ((1 : ℝ) / 3) * (c ^ 3) ^ ((1 : ℝ) / 3) by refine Real.mul_rpow (by positivity) (by positivity)] at h
            rw [show c ^ 3 = c ^ (3 : ℝ) by norm_cast] at h
            rw [show (c ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) = c ^ ((3 : ℝ) * (1 / 3)) by refine Eq.symm (Real.rpow_mul (by linarith) 3 (1 / 3))] at h
            rw [show (3 : ℝ) * (1 / 3) = 1 by ring] at h

            -- Further simplification and cleanup
            simp at h
            field_simp at h
            replace h : c * ((x + y + 1) - 4 * ((x * y) ^ ((1 : ℝ) / 3))) = 0:= by linarith
            have gc : c ≠ 0:= by positivity
            replace h : (x + y + 1) - 4 * ((x * y) ^ ((1 : ℝ) / 3)) = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero gc h

            -- Clean up unnecessary hypotheses
            clear gc hx hy g1 g2 g3 g4 ha hb hc

            -- Derive that x ≥ 1 and y ≥ 1 from x^2 ≥ 1 and y^2 ≥ 1
            replace gx : x ^ 2 ≥ 1 ^ 2:= by linarith
            replace gy : y ^ 2 ≥ 1 ^ 2:= by linarith
            clear h1
            replace gx : |x| ≥ |1|:= by exact sq_le_sq.mp gx
            replace gy : |y| ≥ |1|:= by exact sq_le_sq.mp gy
            simp at gx gy
            rw [show |x| = x by exact abs_of_nonneg (by linarith)] at gx
            rw [show |y| = y by exact abs_of_nonneg (by linarith)] at gy

            -- Final substitution and algebraic manipulation
            set t:= (x * y) ^ ((1 : ℝ) / 3) with ht
            clear_value t
            replace h : x + y = 4 * t - 1:= by linarith
            have ht1 : t ^ 3 = x * y:= by
                rw [show t ^ 3 = t ^ (3 : ℝ) by norm_cast]
                rw [ht]
                rw [Eq.symm (Real.rpow_mul (by positivity) (1 / 3) 3)]
                rw [show ((1 : ℝ) / 3) * 3 = 1 by ring]
                simp

            -- Complete the proof using the fact that t(t-2)^2 ≥ 0
            rw [show 2 * x * y + 2 * y + 2 * x = 2 * t ^ 3 + 2 * (4 * t - 1) by linarith]
            rw [show x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) by ring]
            rw [h, ←ht1]
            have htpos : t > 0:= by rw [ht] ; positivity
            have h : t * (t - 2) ^ 2 ≥ 0:= by positivity
            linarith
        -- Case analysis: The minimum must be one of a^2, b^2, or c^2
        have h2 : min (min (a ^ 2) (b ^ 2)) (c ^ 2) = a ^ 2 ∨ min (min (a ^ 2) (b ^ 2)) (c ^ 2) = b ^ 2 ∨ min (min (a ^ 2) (b ^ 2)) (c ^ 2) = c ^ 2:= by
            by_cases g1 : a ^ 2 ≤ b ^ 2
            .
                rw [show min (a ^ 2) (b ^ 2) = a ^ 2 by exact min_eq_left g1]
                by_cases g2 : a ^ 2 ≤ c ^ 2
                .
                    rw [show min (a ^ 2) (c ^ 2) = a ^ 2 by exact min_eq_left g2]
                    simp
                .
                    simp at g2
                    rw [show min (a ^ 2) (c ^ 2) = c ^ 2 by exact min_eq_right (by linarith)]
                    simp
            .
                simp at g1
                replace g1 : b ^ 2 ≤ a ^ 2:= by linarith
                rw [show min (a ^ 2) (b ^ 2) = b ^ 2 by exact min_eq_right g1]
                by_cases g2 : b ^ 2 ≤ c ^ 2
                .
                    rw [show min (b ^ 2) (c ^ 2) = b ^ 2 by exact min_eq_left g2]
                    simp
                .
                    simp at g2
                    rw [show min (b ^ 2) (c ^ 2) = c ^ 2 by exact min_eq_right (by linarith)]
                    simp
        rcases h2 with h2 | h2 | h2
        -- Case 1: When a^2 is the minimum
        .
            have h3 : min (min (b ^ 2) (c ^ 2)) (a ^ 2) = a ^ 2:= by
                have g2 : a ^ 2 ≤ c ^ 2:= by
                    rw [←h2]
                    exact min_le_right (min (a ^ 2) (b ^ 2)) (c ^ 2)
                have g3 : min (min (a ^ 2) (b ^ 2)) (c ^ 2) ≤ min (a ^ 2) (b ^ 2):= by exact min_le_left (min (a ^ 2) (b ^ 2)) (c ^ 2)
                rw [h2] at g3
                have g4 : min (a ^ 2) (b ^ 2) ≤ b ^ 2:= by exact min_le_right (a ^ 2) (b ^ 2)
                replace g3 : a ^ 2 ≤ b ^ 2:= by linarith
                clear g4
                have g4 : a ^ 2 ≤ min (b ^ 2) (c ^ 2):= by exact le_min g3 g2
                exact min_eq_right g4
            -- Apply the main lemma with cyclic permutation of variables
            specialize h1 b c a ⟨hb, hc, ha, (by rw [show b * c * a = a * b * c by ring] ; linarith)⟩ h3
            rw [h2]
            linarith
        -- Case 2: When b^2 is the minimum
        .
            have h3 : min (min (a ^ 2) (c ^ 2)) (b ^ 2) = b ^ 2:= by
                have g2 : b ^ 2 ≤ c ^ 2:= by
                    rw [←h2]
                    exact min_le_right (min (a ^ 2) (b ^ 2)) (c ^ 2)
                have g3 : min (min (a ^ 2) (b ^ 2)) (c ^ 2) ≤ min (a ^ 2) (b ^ 2):= by exact min_le_left (min (a ^ 2) (b ^ 2)) (c ^ 2)
                rw [h2] at g3
                have g4 : min (a ^ 2) (b ^ 2) ≤ a ^ 2:= by exact min_le_left (a ^ 2) (b ^ 2)
                replace g3 : b ^ 2 ≤ a ^ 2:= by linarith
                clear g4
                have g4 : b ^ 2 ≤ min (a ^ 2) (c ^ 2):= by exact le_min g3 g2
                exact min_eq_right g4
            -- Apply the main lemma with cyclic permutation of variables
            specialize h1 a c b ⟨ha, hc, hb, (by rw [show a * c * b = a * b * c by ring] ; linarith)⟩ h3
            rw [h2]
            linarith
        -- Case 3: When c^2 is the minimum
        .
            -- Apply the main lemma directly
            specialize h1 a b c ⟨ha, hb, hc, h⟩ h2
            rw [h2]
            exact h1
