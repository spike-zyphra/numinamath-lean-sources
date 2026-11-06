import Mathlib

open Real

theorem algebra_166030 {a : ℕ → ℝ}
    (ha : ∀ n, a n = 1 / ((n + 1) * sqrt n + n * sqrt (n + 1))) :
    ∑ k in Finset.Icc 1 99, a k = 9 / 10 := by

  have h1 : ∀ n : ℕ, n ≥ 1 → a n = (1 / Real.sqrt (↑n : ℝ)) - (1 / Real.sqrt ((↑n + 1 : ℝ))) := by
    intro n hn
    rw [ha]
    by_cases h : n = 0
    · -- Case n = 0, but we have n ≥ 1, so this case is impossible.
      exfalso
      omega
    · -- Case n > 0
      have h2 : n > 0 := by
        omega
      have h3 : (n : ℝ) > 0 := by
        exact_mod_cast show (0 : ℝ) < (n : ℝ) by
          exact_mod_cast show 0 < n by omega
      have h4 : (n + 1 : ℝ) > 0 := by
        nlinarith
      have eq2 : Real.sqrt (↑n : ℝ) > 0 := by
        apply Real.sqrt_pos.mpr
        positivity
      have eq3 : Real.sqrt ((↑n + 1 : ℝ)) > 0 := by
        apply Real.sqrt_pos.mpr
        positivity
      have eq5 : (1 / Real.sqrt (↑n : ℝ) - 1 / Real.sqrt (↑n + 1 : ℝ)) = (Real.sqrt (↑n + 1 : ℝ) - Real.sqrt (↑n : ℝ)) / ((Real.sqrt (↑n : ℝ)) * (Real.sqrt (↑n + 1 : ℝ))) := by
        field_simp [show Real.sqrt (↑n : ℝ) ≠ 0 by positivity, show Real.sqrt (↑n + 1 : ℝ) ≠ 0 by positivity]
        all_goals
          nlinarith [Real.sqrt_nonneg (↑n : ℝ), Real.sqrt_nonneg (↑n + 1 : ℝ)]
      have eq9 : 1 / ((↑n + 1 : ℝ) * Real.sqrt (↑n : ℝ) + (↑n : ℝ) * Real.sqrt (↑n + 1 : ℝ)) = (Real.sqrt (↑n + 1 : ℝ) - Real.sqrt (↑n : ℝ)) / ((Real.sqrt (↑n : ℝ)) * (Real.sqrt (↑n + 1 : ℝ))) := by
        have eq6 : Real.sqrt (↑n : ℝ) * Real.sqrt (↑n + 1 : ℝ) > 0 := by
          positivity
        have eq9 : (Real.sqrt (↑n + 1 : ℝ) - Real.sqrt (↑n : ℝ)) * ((↑n + 1 : ℝ) * Real.sqrt (↑n : ℝ) + (↑n : ℝ) * Real.sqrt (↑n + 1 : ℝ)) = Real.sqrt (↑n : ℝ) * Real.sqrt (↑n + 1 : ℝ) := by
          have h10 : Real.sqrt (↑n + 1 : ℝ) ^ 2 = (↑n + 1 : ℝ) := by
            rw [Real.sq_sqrt]
            positivity
          have h11 : Real.sqrt (↑n : ℝ) ^ 2 = (↑n : ℝ) := by
            rw [Real.sq_sqrt]
            positivity
          nlinarith [mul_nonneg (Real.sqrt_nonneg (↑n : ℝ)) (Real.sqrt_nonneg (↑n + 1 : ℝ)), Real.sq_sqrt (show 0 ≤ (↑n : ℝ) by positivity), Real.sq_sqrt (show 0 ≤ (↑n + 1 : ℝ) by positivity), sq_nonneg (Real.sqrt (↑n : ℝ) ^ 2 - (↑n : ℝ)), sq_nonneg (Real.sqrt (↑n + 1 : ℝ) ^ 2 - (↑n + 1 : ℝ)), mul_pos eq2 eq3]
        have eq7 : (↑n + 1 : ℝ) * Real.sqrt (↑n : ℝ) + (↑n : ℝ) * Real.sqrt (↑n + 1 : ℝ) ≠ 0 := by
          positivity
        field_simp [(show Real.sqrt (↑n : ℝ) * Real.sqrt (↑n + 1 : ℝ) ≠ 0 by positivity), eq7]
        nlinarith
      linarith [eq5, eq9]

  have h2 : ∀ (k : ℕ), ∑ i in Finset.Icc 1 k, a i = 1 - (1 / Real.sqrt ((↑k + 1 : ℝ))) := by
    intro k
    induction k with
    | zero =>
      norm_num [Finset.sum_eq_zero]
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      rw [ih]
      rw [h1 (k + 1) (by omega)]
      field_simp [Real.sqrt_nonneg ((↑k + 1 + 1 : ℝ)), Real.sqrt_nonneg ((↑k + 1 : ℝ))]
      all_goals
        ring_nf

  have h3 : ∑ k in Finset.Icc 1 99, a k = 1 - (1 / Real.sqrt (100 : ℝ)) := by
    specialize h2 99
    norm_num at h2 ⊢
    linarith

  have h4 : Real.sqrt (100 : ℝ) = 10 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num

  rw [h4] at h3
  norm_num at h3 ⊢
  all_goals
    linarith