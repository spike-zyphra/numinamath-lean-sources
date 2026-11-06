import Mathlib
/- Soit $a, b, c$ des réels tels que $-1 \leqslant a x^{2}+b x+c \leqslant 1$ pour $x=-1, x=0$ et $x=1$. Prouver que

$$
-\frac{5}{4} \leqslant a x^{2}+b x+c \leqslant \frac{5}{4} \text { pour tout réel } x \in[ -1,1]
$$ -/
theorem algebra_607509 (a b c : ℝ) (h : ∀ x : ℝ, x = -1 ∨ x = 0 ∨ x = 1 → -1 ≤ a * x ^ 2 + b * x + c ∧ a * x ^ 2 + b * x + c ≤ 1) : ∀ x ∈ Set.Icc (-1) 1, -5 / 4 ≤ a * x ^ 2 + b * x + c ∧ a * x ^ 2 + b * x + c ≤ 5 / 4:= by
    intro x
    -- Define P(x) = ax² + bx + c for easier notation
    set P:= fun (x : ℝ) => a * x ^ 2 + b * x + c with hP
    clear_value P
    intro hx
    simp at hx
    rcases hx with ⟨hx1, hx2⟩
    -- Prove that |P(x)| ≤ 1 at x = -1, 0, 1
    replace h : ∀ x : ℝ, x = -1 ∨ x = 0 ∨ x = 1 → |P x| ≤ 1:= by
        intro x
        intro hx
        specialize h x hx
        simp [hP]
        rcases h with ⟨h1, h2⟩
        replace h1 : a * x ^ 2 + b * x + c + 1 ≥ 0:= by linarith
        replace h2 : 1 - (a * x ^ 2 + b * x + c) ≥ 0:= by linarith
        have h3 : (a * x ^ 2 + b * x + c + 1) * (1 - (a * x ^ 2 + b * x + c)) ≥ 0:= by positivity
        rw [show (1 : ℝ) = |1| by simp]
        suffices (a * x ^ 2 + b * x + c) ^ 2 ≤ 1 ^ 2 by exact sq_le_sq.mp this
        linarith
    -- Store the values of |P(x)| at x = -1, 0, 1
    have hP1:= h 1 (by simp)
    have hP2:= h (-1) (by simp)
    have hP3:= h 0 (by simp)
    clear h
    -- Lagrange interpolation formula for P(x)
    have h1 : P x = x * (x + 1) / 2 * P 1 - x * (1 - x) / 2 * P (-1) + (1 - x ^ 2) * P 0:= by
        simp [hP]
        linarith
    -- Split into two cases: x ≥ 0 and x < 0
    by_cases hx3 : x ≥ 0
    .
        -- Case x ≥ 0: Prove various inequalities needed for the bound
        have g1 : 1 - x ^ 2 ≥ 0:= by
            replace _ : x + 1 ≥ 0:= by linarith
            replace hx2 : 1 - x ≥ 0:= by linarith
            have g1 : (x + 1) * (1 - x) ≥ 0:= by positivity
            linarith
        have g2 : x * (x + 1) / 2 ≥ 0:= by positivity
        have g3 : x * (1 - x) / 2 ≥ 0:= by
            replace hx2 : 1 - x ≥ 0:= by linarith
            positivity
        -- Triangle inequality and absolute value manipulations
        have h2 : |P x| ≤ x * (x + 1) / 2 * |P 1| + x * (1 - x) / 2 * |P (-1)| + (1 - x ^ 2) * |P 0|:= by
            rw [h1]
            have h2:= abs_add_le (x * (x + 1) / 2 * P 1 - x * (1 - x) / 2 * P (-1)) ((1 - x ^ 2) * P 0)
            have h3:= abs_sub (x * (x + 1) / 2 * P 1) (x * (1 - x) / 2 * P (-1))
            rw [abs_mul (1 - x ^ 2) (P 0)] at h2
            rw [abs_mul (x * (x + 1) / 2) (P 1)] at h3
            rw [abs_mul (x * (1 - x) / 2) (P (-1))] at h3
            rw [abs_of_nonneg g1] at h2
            rw [abs_of_nonneg g2] at h3
            rw [abs_of_nonneg g3] at h3
            linarith
        -- Apply bounds from x = -1, 0, 1 to get final inequality
        have h3 : x * (x + 1) / 2 * |P 1| ≤ x * (x + 1) / 2 * 1:= by exact mul_le_mul_of_nonneg_left hP1 g2
        have h4 : x * (1 - x) / 2 * |P (-1)| ≤ x * (1 - x) / 2 * 1:= by exact mul_le_mul_of_nonneg_left hP2 g3
        have h5 : (1 - x ^ 2) * |P 0| ≤ (1 - x ^ 2) * 1:= by exact mul_le_mul_of_nonneg_left hP3 g1
        have h6 : (x - 1 / 2) ^ 2 ≥ 0:= by positivity
        have h7 : |P x| ≤ 5 / 4:= by linarith
        simp [hP] at h7
        constructor
        .
            replace h7 : -(a * x ^ 2 + b * x + c) ≤ 5 / 4:= by exact le_of_max_le_right h7
            linarith
        .
            replace h7 : a * x ^ 2 + b * x + c ≤ 5 / 4:= by exact le_of_max_le_left h7
            linarith
    .
        -- Case x < 0: Similar to the previous case but with adjusted signs
        simp at hx3
        have g1 : -x * (x + 1) / 2 ≥ 0:= by
            replace h3 : -x ≥ 0:= by linarith
            replace hx1 : x + 1 ≥ 0:= by linarith
            positivity
        have g2 : -x * (1 - x) / 2 ≥ 0:= by
            replace hx3 : -x ≥ 0:= by linarith
            replace hx2 : 1 - x ≥ 0:= by linarith
            positivity
        have g3 : (1 - x ^ 2) ≥ 0:= by
            replace hx1 : x + 1 ≥ 0:= by linarith
            replace hx2 : 1 - x ≥ 0:= by linarith
            have _ : (x + 1) * (1 - x) ≥ 0:= by positivity
            linarith
        -- Similar triangle inequality and absolute value manipulations for x < 0
        have h2 : |P x| ≤ -x * (x + 1) / 2 * |P 1| + -x * (1 - x) / 2 * |P (-1)| + (1 - x ^ 2) * |P 0|:= by
            rw [h1]
            have h2:= abs_add_le (x * (x + 1) / 2 * P 1 - x * (1 - x) / 2 * P (-1)) ((1 - x ^ 2) * P 0)
            have h3:= abs_sub (x * (x + 1) / 2 * P 1) (x * (1 - x) / 2 * P (-1))
            rw [abs_mul (1 - x ^ 2) (P 0)] at h2
            rw [abs_mul (x * (x + 1) / 2) (P 1)] at h3
            rw [abs_mul (x * (1 - x) / 2) (P (-1))] at h3
            rw [abs_of_nonneg g3] at h2
            rw [show |x * (x + 1) / 2| = -(x * (x + 1) / 2) by refine abs_of_nonpos (by linarith)] at h3
            rw [show |x * (1 - x) / 2| = -(x * (1 - x) / 2) by refine abs_of_nonpos (by linarith)] at h3
            linarith
        -- Final bounds for x < 0 case
        have h3 : (1 - x ^ 2) * |P 0| ≤ (1 - x ^ 2) * 1:= by exact mul_le_mul_of_nonneg_left hP3 g3
        have h4 : -x * (x + 1) / 2 * |P 1| ≤ -x * (x + 1) / 2 * 1:= by exact mul_le_mul_of_nonneg_left hP1 g1
        have h5 : -x * (1 - x) / 2 * |P (-1)| ≤ -x * (1 - x) / 2 * 1:= by exact mul_le_mul_of_nonneg_left hP2 g2
        have h6 : (x + 1 / 2) ^ 2 ≥ 0:= by positivity
        have h7 : |P x| ≤ 5 / 4:= by linarith
        simp [hP] at h7
        constructor
        .
            replace h7 : -(a * x ^ 2 + b * x + c) ≤ 5 / 4:= by exact le_of_max_le_right h7
            linarith
        .
            replace h7 : a * x ^ 2 + b * x + c ≤ 5 / 4:= by exact le_of_max_le_left h7
            linarith
