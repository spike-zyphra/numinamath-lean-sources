import Mathlib

open Finset Real

theorem inequalities_75411 {n : ℕ} (hn : 0 < n) (a : ℕ → ℝ)
    (ha : ∀ i ∈ Icc 1 n, 0 < a i) (h : ∏ i ∈ Icc 1 n, a i = 1) :
    ∏ i ∈ Icc 1 n, (2 + a i) ≥ 3 ^ n := by

  have h1 : ∀ i ∈ Icc 1 n, (2 + a i) ≥ 3 * (a i) ^ (1 / 3 : ℝ) := by
    intro i hi
    have h2 : 0 < a i := ha i hi
    have h5 : (2 + a i) ≥ 3 * (a i) ^ (1 / 3 : ℝ) := by
      have h4 : ((a i) ^ (1 / 3 : ℝ)) ^ 3 = a i := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals
          positivity
      nlinarith [sq_nonneg ((a i) ^ (1 / 3 : ℝ) - 1), sq_nonneg (( (a i) ^ (1 / 3 : ℝ) ) ^ 2 - (a i) ^ (1 / 3 : ℝ) ), sq_nonneg (( (a i) ^ (1 / 3 : ℝ) ) ^ 2 - 1), Real.rpow_nonneg (show 0 ≤ a i by linarith) (1 / 3 : ℝ), sq_nonneg ((a i) ^ (1 / 3 : ℝ) * (1 - (a i) ^ (1 / 3 : ℝ) ) ) ]
    linarith

  have h2 : ∏ i ∈ Icc 1 n, (2 + a i) ≥ ∏ i ∈ Icc 1 n, (3 * (a i) ^ (1 / 3 : ℝ)) := by
    apply Finset.prod_le_prod
    · -- Show each term is non-negative
      intro i hi
      have h2 : 0 < a i := ha i hi
      have h4 : 0 < (a i) ^ (1 / 3 : ℝ) := by positivity
      positivity
    · -- Show (2 + a i) ≥ 3 * (a i) ^ (1 / 3 : ℝ) for each i
      intro i hi
      have h10 : (2 + a i) ≥ 3 * (a i) ^ (1 / 3 : ℝ) := by
        have h2 : 0 < a i := ha i hi
        have h5 : (2 + a i) ≥ 3 * (a i) ^ (1 / 3 : ℝ) := by
          have h4 : ((a i) ^ (1 / 3 : ℝ)) ^ 3 = a i := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul]
            norm_num
            all_goals
              positivity
          nlinarith [sq_nonneg ((a i) ^ (1 / 3 : ℝ) - 1), sq_nonneg (( (a i) ^ (1 / 3 : ℝ) ) ^ 2 - (a i) ^ (1 / 3 : ℝ) ), sq_nonneg (( (a i) ^ (1 / 3 : ℝ) ) ^ 2 - 1), Real.rpow_nonneg (show 0 ≤ a i by linarith) (1 / 3 : ℝ), sq_nonneg ((a i) ^ (1 / 3 : ℝ) * (1 - (a i) ^ (1 / 3 : ℝ) ) ) ]
        linarith
      linarith

  have h3 : ∏ i ∈ Icc 1 n, (3 * (a i) ^ (1 / 3 : ℝ)) = (3 ^ n) * (∏ i ∈ Icc 1 n, (a i) ^ (1 / 3 : ℝ)) := by
    calc
      ∏ i ∈ Icc 1 n, (3 * (a i) ^ (1 / 3 : ℝ))
          = ∏ i ∈ Icc 1 n, (3 * ((a i) ^ (1 / 3 : ℝ)) ) := by rfl
      _ = (∏ i ∈ Icc 1 n, (3 : ℝ)) * (∏ i ∈ Icc 1 n, ((a i) ^ (1 / 3 : ℝ)) ) := by
        rw [Finset.prod_mul_distrib]
      _ = (3 ^ n) * (∏ i ∈ Icc 1 n, (a i) ^ (1 / 3 : ℝ)) := by
        simp [Finset.prod_const]
        all_goals
          rfl

  have h4 : ∏ i ∈ Icc 1 n, (a i) ^ (1 / 3 : ℝ) = 1 := by
    have h5 : ∏ i ∈ Icc 1 n, (a i) ^ (1 / 3 : ℝ) = (∏ i ∈ Icc 1 n, a i) ^ (1 / 3 : ℝ) := by
      rw [Real.finset_prod_rpow]
      intro i hi
      have h1 : 0 ≤ a i := by
        have ha2 : 0 < a i := ha i hi
        linarith
      exact h1
    rw [h5, h]
    norm_num

  have h7 : ∏ i ∈ Icc 1 n, (3 * (a i) ^ (1 / 3 : ℝ)) = (3 ^ n : ℝ) := by
    rw [h3, h4]
    all_goals
      norm_num

  linarith