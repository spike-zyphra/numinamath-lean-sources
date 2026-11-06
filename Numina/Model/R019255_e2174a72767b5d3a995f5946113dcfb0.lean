import Mathlib

open Real

theorem algebra_598499 (a : ℕ → ℝ) (ha : ∀ n, 1 ≤ n → a n = 1 / ((n + 1) * sqrt n + n * sqrt (n + 1))) :
    ∑ i in Finset.Icc 1 99, a i = 9 / 10 := by

  have h1 : ∀ n : ℕ, 1 ≤ n → a n = (1 / Real.sqrt (↑n : ℝ)) - (1 / Real.sqrt ((↑n + 1 : ℝ)) ) := by
    intro n hn
    have h2 : a n = 1 / ((↑n + 1) * Real.sqrt (↑n : ℝ) + (↑n) * Real.sqrt ((↑n + 1 : ℝ)) ) := by
      specialize ha n (by linarith)
      simpa using ha
    rw [h2]
    have h3 : (↑n : ℝ) ≥ (1 : ℝ) := by exact_mod_cast (show (1 : ℕ) ≤ n by linarith)
    have h4 : (↑n + 1 : ℝ) ≥ (1 + 0 : ℝ) := by nlinarith
    have h7 : Real.sqrt (↑n : ℝ) ^ 2 = (↑n : ℝ) := by
      rw [Real.sq_sqrt]
      have h10 : (↑n : ℝ) ≥ 0 := by positivity
      nlinarith
    have h8 : Real.sqrt ((↑n + 1 : ℝ)) ^ 2 = (↑n + 1 : ℝ) := by
      rw [Real.sq_sqrt]
      have h10 : (↑n + 1 : ℝ) ≥ 0 := by positivity
      nlinarith
    have h47 : Real.sqrt (↑n : ℝ) > 0 := by
      apply Real.sqrt_pos.mpr
      have h12 : (↑n : ℝ) > 0 := by
        have h7 : (↑n : ℝ) ≥ (1 : ℝ) := by exact_mod_cast (show (1 : ℕ) ≤ n by linarith)
        nlinarith
      nlinarith
    have h48 : Real.sqrt ((↑n + 1 : ℝ)) > 0 := by
      apply Real.sqrt_pos.mpr
      have h100 : (↑n + 1 : ℝ) > 0 := by
        have h10 : (↑n : ℝ) ≥ (1 : ℝ) := by exact_mod_cast (show (1 : ℕ) ≤ n by linarith)
        nlinarith
      nlinarith
    have h51 : ((↑n + 1) * Real.sqrt (↑n : ℝ) + (↑n) * Real.sqrt ((↑n + 1 : ℝ)) ) ≠ 0 := by
      have h13 : ((↑n + 1) * Real.sqrt (↑n : ℝ) + (↑n) * Real.sqrt ((↑n + 1 : ℝ)) ) > 0 := by
        have h96 : Real.sqrt (↑n : ℝ) > 0 := h47
        have h97 : Real.sqrt ((↑n + 1 : ℝ)) > 0 := h48
        have h99 : (↑n + 1) * Real.sqrt (↑n : ℝ) > 0 := by
          apply mul_pos
          · have h14 : (↑n + 1 : ℝ) > 0 := by
              have h70 : (↑n : ℝ) ≥ (1 : ℝ) := by exact_mod_cast (show (1 : ℕ) ≤ n by linarith)
              nlinarith
            nlinarith
          · linarith [h96]
        have h101 : (↑n) * Real.sqrt ((↑n + 1 : ℝ)) ≥ 0 := by
          apply mul_nonneg
          · have h139 : (↑n : ℝ) ≥ (1 : ℝ) := by exact_mod_cast (show (1 : ℕ) ≤ n by linarith)
            nlinarith
          · positivity
        positivity
      linarith
    field_simp [Real.sqrt_nonneg (↑n : ℝ), Real.sqrt_nonneg ((↑n + 1 : ℝ)), h7, h8, mul_nonneg (show (0 : ℝ) ≤ (↑n) by positivity) (show (0 : ℝ) ≤ Real.sqrt (↑n : ℝ) by positivity) ]
    <;> nlinarith [ sq_nonneg (Real.sqrt (↑n : ℝ) ^ 2), sq_nonneg (Real.sqrt ((↑n + 1 : ℝ)) ^ 2), Real.sqrt_nonneg (↑n : ℝ), Real.sqrt_nonneg ((↑n + 1 : ℝ)), mul_nonneg (Real.sqrt_nonneg (↑n : ℝ)) (Real.sqrt_nonneg (↑n + 1 : ℝ)) ]
  have h9 : ∑ i in Finset.Icc 1 99, a i = (1 : ℝ) - (1 / Real.sqrt ((100 : ℝ)) ) := by
    have h8 : ∀ (k : ℕ), ∑ i in Finset.Icc 1 k, a i = (1 : ℝ) - (1 / Real.sqrt ((↑k + 1 : ℝ)) ) := by
      intro k
      induction k with
      | zero =>
        norm_num [Finset.sum_eq_zero]
      | succ k ih =>
        rw [Finset.sum_Icc_succ_top (by linarith)]
        rw [h1 (k + 1) (by linarith)]
        rw [ih]
        field_simp [Real.sqrt_nonneg ((↑k + 1 : ℝ) ), Real.sqrt_nonneg ((↑k + 2 : ℝ) ) ]
        all_goals
          ring
    specialize h8 99
    norm_num at h8 ⊢
    linarith
  have h11 : Real.sqrt (100 : ℝ) = 10 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  rw [h9]
  rw [h11]
  all_goals
    norm_num