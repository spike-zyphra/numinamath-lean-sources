import Mathlib

open Real

theorem inequalities_603965 (n : ℕ) (hn : 0 < n) :
    2 * n / 3 * sqrt n < ∑ i in Finset.Icc 1 n, sqrt i ∧
    ∑ i in Finset.Icc 1 n, sqrt i < (4 * n + 3) / 6 * sqrt n := by
  have h1 : 0 < (n : ℝ) := by exact_mod_cast hn
  constructor
  · -- Prove that $\frac{2n}{3}\sqrt{n} < \sum_{i=1}^{n} \sqrt{i}$
    have h2 : 2 * n / 3 * Real.sqrt (n : ℝ) < ∑ i in Finset.Icc 1 n, Real.sqrt (i : ℝ) := by
      have h3 : ∀ (n : ℕ), 0 < n → 2 * n / 3 * Real.sqrt (n : ℝ) < ∑ i in Finset.Icc 1 n, Real.sqrt (i : ℝ) := by
        intro n hn
        induction n with
        | zero =>
          linarith
        | succ n ih =>
          by_cases h : n = 0
          · -- Case n = 1
            rw [h]
            norm_num [Finset.sum_Icc_succ_top, Real.sqrt_one]
            all_goals norm_num [Real.sqrt_one, mul_add, add_mul, mul_comm]
            <;> nlinarith [Real.sqrt_nonneg (1 : ℝ), Real.sq_sqrt (show 0 ≤ (1 : ℝ) by norm_num)]
          · -- Case n > 0
            have hn' : 0 < n := by
              by_contra h'
              push_neg at h'
              have : n = 0 := by linarith
              tauto
            have ih' := ih hn'
            rw [Finset.sum_Icc_succ_top (by linarith)]
            simp at ih' ⊢
            have h3 : (n : ℝ) ≥ (1 : ℝ) := by exact_mod_cast (show (n : ℕ) ≥ (1 : ℕ) by linarith)
            nlinarith [Real.sqrt_nonneg (n : ℝ), Real.sqrt_nonneg (n + 1 : ℝ), sq_nonneg (Real.sqrt (n + 1 : ℝ) - Real.sqrt (n : ℝ)), sq_nonneg (n - 1 : ℝ), 
                Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by linarith), 
                Real.sq_sqrt (show (0 : ℝ) ≤ (n + 1 : ℝ) by linarith), 
                mul_nonneg (Real.sqrt_nonneg (n : ℝ)) (Real.sqrt_nonneg (n + 1 : ℝ)), 
                sq_nonneg (Real.sqrt (n + 1 : ℝ) ^ 2 - Real.sqrt (n : ℝ) ^ 2)
                ]
      apply h3
      all_goals linarith
    exact_mod_cast h2
  · -- Prove that ∑ i in Finset.Icc 1 n, sqrt i < (4 * n + 3) / 6 * sqrt n
    have h4 : ∑ i in Finset.Icc 1 n, Real.sqrt (i : ℝ) < (4 * n + 3) / 6 * Real.sqrt (n : ℝ) := by
      have h5 : ∀ (n : ℕ), 0 < n → ∑ i in Finset.Icc 1 n, Real.sqrt (i : ℝ) < (4 * n + 3) / 6 * Real.sqrt (n : ℝ) := by
        intro n hn
        induction n with
        | zero =>
          linarith
        | succ n ih =>
          by_cases h : n = 0
          · -- Case n = 1
            rw [h]
            norm_num [Finset.sum_Icc_succ_top, Real.sqrt_one]
            all_goals norm_num [Real.sqrt_one, mul_add, add_mul, mul_comm]
            <;> nlinarith [Real.sqrt_nonneg (1 : ℝ), Real.sq_sqrt (show 0 ≤ (1 : ℝ) by norm_num)]
          · -- Case n > 0
            have hn' : 0 < n := by
              by_contra h'
              push_neg at h'
              have : n = 0 := by linarith
              tauto
            have ih' := ih hn'
            rw [Finset.sum_Icc_succ_top (by linarith)]
            simp at ih' ⊢
            have h3 : (n : ℝ) ≥ (1 : ℝ) := by exact_mod_cast (show (n : ℕ) ≥ (1 : ℕ) by linarith)
            have h7 : (4 * (n : ℝ) + 3) * Real.sqrt (n : ℝ) < (4 * (n : ℝ) + 1) * Real.sqrt (n + 1 : ℝ) := by
              have h8 : (4 * (n : ℝ) + 3) ^ 2 * (n : ℝ) < (4 * (n : ℝ) + 1) ^ 2 * (n + 1 : ℝ) := by
                nlinarith [sq_nonneg ( (n : ℝ) - 1 ), sq_nonneg ( (n : ℝ) ^ 2 - ( (n + 1 : ℝ) ) ^ 2 ) ]
              have h9 : (4 * (n : ℝ) + 3) * Real.sqrt (n : ℝ) ≥ 0 := by
                have hn0 : (n : ℝ) ≥ 0 := by linarith
                have hsqrt : Real.sqrt (n : ℝ) ≥ 0 := Real.sqrt_nonneg (n : ℝ)
                nlinarith [Real.sqrt_nonneg (n : ℝ)]
              have h10 : (4 * (n : ℝ) + 1) * Real.sqrt (n + 1 : ℝ) ≥ 0 := by
                have hn10 : (n + 1 : ℝ) ≥ 0 := by linarith
                have hsqrt1 : Real.sqrt (n + 1 : ℝ) ≥ 0 := Real.sqrt_nonneg (n + 1 : ℝ)
                nlinarith [Real.sqrt_nonneg (n + 1 : ℝ)]
              have h11 : ((4 * (n : ℝ) + 3) * Real.sqrt (n : ℝ)) ^ 2 < ((4 * (n : ℝ) + 1) * Real.sqrt (n + 1 : ℝ)) ^ 2 := by
                have h13 : ((4 * (n : ℝ) + 3) * Real.sqrt (n : ℝ)) ^ 2 = (4 * (n : ℝ) + 3) ^ 2 * (Real.sqrt (n : ℝ) ^ 2) := by ring_nf
                rw [h13]
                have h14 : ((4 * (n : ℝ) + 1) * Real.sqrt (n + 1 : ℝ)) ^ 2 = (4 * (n : ℝ) + 1) ^ 2 * (Real.sqrt (n + 1 : ℝ) ^ 2) := by ring_nf
                rw [h14]
                have h15 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (by linarith)
                rw [h15] at *
                have h16 : Real.sqrt (n + 1 : ℝ) ^ 2 = (n + 1 : ℝ) := Real.sq_sqrt (by linarith)
                rw [h16] at *
                linarith [h8, sq_nonneg (n - (1 : ℝ)), sq_nonneg ((n + 1 : ℝ) - (n : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (n + 1 : ℝ) by linarith) ]
              nlinarith [h11, Real.sqrt_nonneg (n : ℝ), Real.sqrt_nonneg (n + 1 : ℝ), sq_nonneg ((4 * (n : ℝ) + 3) * Real.sqrt (n : ℝ) - (4 * (n : ℝ) + 1) * Real.sqrt (n + 1 : ℝ)), sq_nonneg (Real.sqrt (n : ℝ) - Real.sqrt (n + 1 : ℝ) ), Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (n + 1 : ℝ) by linarith) ]
            nlinarith [Real.sqrt_nonneg (↑n : ℝ), Real.sqrt_nonneg (↑n + 1 : ℝ), sq_nonneg (Real.sqrt (↑n + 1 : ℝ) - Real.sqrt (↑n : ℝ) ), sq_nonneg ((↑n + 1) - (↑n : ℝ)), sq_nonneg ((4*↑n+3)*(↑n) - (4*↑n+1)*(↑n+1)), Real.sq_sqrt (show (0 : ℝ) ≤ (↑n : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (↑n + 1 : ℝ) by linarith), Real.sqrt_nonneg (↑n + 1 : ℝ), mul_nonneg (Real.sqrt_nonneg (↑n : ℝ)) (Real.sqrt_nonneg (↑n + 1 : ℝ)), h7, mul_nonneg (show (0 : ℝ) ≤ (1 : ℝ) by norm_num) (show (0 : ℝ) ≤ (1 : ℝ) by norm_num) ]
      apply h5
      all_goals linarith
    exact_mod_cast h4