import Mathlib
/- Let $t \geqslant \frac{1}{2}$ be a real number and $n$ a positive integer. Prove that

$$
t^{2 n} \geqslant(t-1)^{2 n}+(2 t-1)^{n}
$$ -/
theorem algebra_240469 (t : ℝ) (ht : t ≥ 1 / 2) (n : ℕ) (hn : n > 0) :
t ^ (2 * n) ≥ (t - 1) ^ (2 * n) + (2 * t - 1) ^ n:= by

    -- Prove a stronger statement by induction on n
    have h1 : ∀ n : ℕ, t ^ (2 * (n + 1)) ≥ (t - 1) ^ (2 * (n + 1)) + (2 * t - 1) ^ (n + 1):= by
        intro n
        induction n with
        -- Base case: n = 0
        | zero =>
            simp
            linarith
        -- Inductive step: prove for n + 1 assuming it holds for n
        | succ n ih =>
            -- Rename n + 1 to m for cleaner notation
            set m:= n + 1 with hm
            clear_value m
            -- Rewrite exponents using algebraic identities
            rw [show 2 * (m + 1) = 2 * m + 2 by ring]
            rw [show t ^ (2 * m + 2) = t ^ (2 * m) * t ^ 2 by ring]
            -- Prove t² is non-negative
            have g1 : t ^ 2 ≥ 0:= by positivity
            -- Apply induction hypothesis with multiplication by t²
            replace ih : t ^ 2 * t ^ (2 * m) ≥ t ^ 2 * ((t - 1) ^ (2 * m) + (2 * t - 1) ^ m):= by exact mul_le_mul_of_nonneg_left ih g1
            -- Key inequality to complete the proof
            suffices t ^ 2 * ((t - 1) ^ (2 * m) + (2 * t - 1) ^ m) ≥ (t - 1) ^ (2 * m + 2) + (2 * t - 1) ^ (m + 1) by linarith
            -- Prove necessary inequalities
            replace g1 : t ^ 2 ≥ (t - 1) ^ 2:= by linarith
            have g2 : t ^ 2 ≥ 2 * t - 1:= by
                have g2 : (t - 1) ^ 2 ≥ 0:= by positivity
                linarith
            -- Show 2t - 1 is non-negative
            replace ht : 2 * t - 1 ≥ 0:= by linarith
            -- Prove non-negativity of terms
            have g3 : (2 * t - 1) ^ m ≥ 0:= by positivity
            have g4 : (t - 1) ^ (2 * m) ≥ 0:= by
                rw [show (t - 1) ^ (2 * m) = ((t - 1) ^ 2) ^ m by exact pow_mul (t - 1) 2 m]
                positivity
            -- Apply multiplication inequalities
            replace g1 : t ^ 2 * (t - 1) ^ (2 * m) ≥ (t - 1) ^ 2 * (t - 1) ^ (2 * m):= by exact mul_le_mul_of_nonneg_right g1 g4
            replace g2 : t ^ 2 * (2 * t - 1) ^ m ≥ (2 * t - 1) * (2 * t - 1) ^ m:= by exact mul_le_mul_of_nonneg_right g2 g3
            -- Rewrite expressions using power rules
            rw [show (2 * t - 1) ^ (m + 1) = (2 * t - 1) * (2 * t - 1) ^ m by ring]
            rw [show (t - 1) ^ (2 * m + 2) = (t - 1) ^ (2 * m) * (t - 1) ^ 2 by ring]
            linarith
    -- Apply the stronger statement to prove the original theorem
    specialize h1 (n - 1)
    rw [show n - 1 + 1 = n by omega] at h1
    exact h1
