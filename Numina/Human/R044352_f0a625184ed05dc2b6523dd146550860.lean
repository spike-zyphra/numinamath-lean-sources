import Mathlib

/- Find the smallest positive integer $n$ such that there exists $r \in (0, \tfrac{1}{1000})$ such that the number $(n+r)^3$ is an integer. -/
theorem algebra_21813 :
    IsLeast {n : ℕ | 0 < n ∧ ∃ r : ℝ, 0 < r ∧ r < 1 / 1000 ∧ ∃ k : ℤ, (n + r) ^ (3 : ℝ) = k} 19 := by
    -- simplify the expression
    simp [IsLeast, lowerBounds]
    -- split the goal into two parts
    constructor
    .   -- prove that 19 is OK
        -- introduce r, k
        let k : ℤ := 6860
        have hk : k = 6860 := rfl
        let r : ℝ := 6860 ^ ((1 : ℝ) / 3) - 19
        have hr : r = 6860 ^ ((1 : ℝ) / 3) - 19 := rfl
        -- prove that r is in the interval
        have hr0 : r > 0 := by
            rw [hr]
            have h1: (19 : ℝ) ^ (3 : ℝ) < 6860 := by norm_num
            have h2 : (19 : ℝ) < (6860 : ℝ) ^ ((1 : ℝ) / 3) := by
                rw [show 1 / 3 = (3 : ℝ)⁻¹ by ring_nf]
                exact (Real.lt_rpow_inv_iff_of_pos (by linarith) (by linarith) (by linarith)).mpr h1
            linarith
        have hr1 : r < 1000⁻¹ := by
            rw [hr]
            have h1 : 6860 < (19 + (1 : ℝ) / 1000) ^ (3 : ℝ) := by norm_num
            have h2 : (6860 : ℝ) ^ ((1 : ℝ) / 3) < 19 + 1 / 1000 := by
                rw [show 1 / 3 = (3 : ℝ)⁻¹ by ring_nf]
                exact (Real.rpow_inv_lt_iff_of_pos (by linarith) (by linarith) (by linarith)).mpr h1
            linarith
        -- prove that r and k satisfy the equation
        have hrk : (19 + r) ^ (3 : ℝ) = ↑k := by
            rw [hr, hk]
            norm_num
            refine (Real.eq_rpow_inv (by positivity) (by linarith) (by linarith)).mp ?_
            rw [show 1 / 3 = (3 : ℝ)⁻¹ by ring_nf]
        -- use r, k to prove the goal
        use r
        refine ⟨hr0, hr1, ?_⟩
        use k
    .   -- prove that n must be at least 19
        intro a _ x hx0 hx1 k hk
        -- prove that a ^ 3 + 1 ≤ k
        -- first prove that a ^ 3 < k
        have hak : (k : ℝ) > a ^ 3 := by
            have ha1 : ↑a ^ 3 < (↑a + x) ^ 3 := pow_lt_pow_left (by linarith) (by linarith) (by linarith)
            rw [←hk]
            have ha2 : (↑a + x) ^ 3 = (↑a + x) ^ (3 : ℝ) := by norm_cast
            rw [←ha2]
            linarith
        -- prove that a ^ 3 < k
        replace hak : a ^ 3 < k := by
            rify
            linarith
        replace hak : a ^ 3 + 1 ≤ k := Int.add_one_le_of_lt hak
        rify at hak
        rw [←hk] at hak
        -- expand the expression
        have ha1 : (↑a + x) ^ 3 = a ^ 3 + 3 * a ^ 2 * x + 3 * a * x ^ 2 + x ^ 3 := by linarith
        have ha2 : (↑a + x) ^ 3 = (↑a + x) ^ (3 : ℝ) := by norm_cast
        rw [←ha2, ha1] at hak
        clear ha1 ha2
        -- prove by contradiction
        by_contra
        -- prove that a ≤ 18
        replace ha1 : a ≤ 18 := by linarith
        -- let them to be real numbers
        rify at ha1
        -- prove that a ^ 2 ≤ 18 ^ 2
        have hineq0 : (a : ℝ) ^ 2 ≤ (18 : ℝ) ^ 2 := sq_le_sq' (show - (18 : ℝ) ≤ a by linarith) (by linarith)
        -- prove that 3 * ↑a ^ 2 ≤ 3 * 18 ^ 2
        have hineq1 : 3 * (a : ℝ) ^ 2 ≤ 3 * (18 : ℝ) ^ 2 := mul_le_mul_of_nonneg_left (hineq0) (by linarith)
        -- prove that 3 * ↑a ^ 2 * x ≤ 0.972
        have hineq2 : 3 * ↑a ^ 2 * x ≤ 0.972 := by
            calc 3 * ↑a ^ 2 * x ≤ 3 * 18 ^ 2 * x := mul_le_mul_of_nonneg_right hineq1 (by linarith)
                _ ≤ 3 * 18 ^ 2 * 1000⁻¹ := by linarith
                _ ≤ 0.972 := by norm_num
        have hineq3 : x ^ 2 ≤ (1000⁻¹) ^ 2 := sq_le_sq' (show - (1000⁻¹) ≤ x by linarith) (by linarith)
        -- prove that a * x ^ 2 ≤ 18 * (1000⁻¹) ^ 2
        have hineq4 : (a : ℝ) * x ^ 2 ≤ 18 * (1000⁻¹) ^ 2 := by
            calc (a : ℝ) * x ^ 2 ≤ a * (1000⁻¹) ^ 2 := mul_le_mul_of_nonneg_left (hineq3) (by linarith)
                _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
        -- prove that 3 * ↑a * x ^ 2 ≤ 0.0001
        have hineq5 : 3 * ↑a * x ^ 2 ≤ 0.0001 := by
            calc 3 * ↑a * x ^ 2 = 3 * (↑a * x ^ 2) := by linarith
                _ ≤ 3 * (18 * (1000⁻¹) ^ 2) := mul_le_mul_of_nonneg_left hineq4 (by linarith)
                _ ≤ 0.0001 := by norm_num
        -- prove that x ^ 3 ≤ (1000⁻¹) ^ 3
        have hineq6 : x ^ 3 ≤ (1000⁻¹) ^ 3 := by
            have g1 : x * x ^ 2 ≤ x * (1000⁻¹) ^ 2 := mul_le_mul_of_nonneg_left hineq3 (by linarith)
            have g2 : x * (1000⁻¹) ^ 2 ≤ (1000⁻¹) ^ 3 := by
                norm_num
                norm_num at hx1
                linarith
            rw [show x ^ 3 = x * x ^ 2 by ring]
            linarith
        -- combine the inequalities
        have hineq : 3 * ↑a ^ 2 * x + 3 * ↑a * x ^ 2 + x ^ 3 < 0.98 := by
            calc _ ≤ 0.972 + 0.0001 + x ^ 3 := by linarith
                _ ≤ 0.972 + 0.0001 + (1000⁻¹) ^ 3 := by linarith
                _ < 0.98 := by norm_num
        -- trivial contradiction
        have g4 : (1 : ℝ) > 0.98 := by norm_num
        linarith
