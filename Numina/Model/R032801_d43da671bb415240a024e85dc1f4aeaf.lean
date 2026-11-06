import Mathlib

open Real

theorem inequalities_189976 :
    IsLeast {n : ℕ | 0 ≤ n ∧ sqrt (n + 99) - sqrt n < 1} 2402 := by
  constructor
  · -- Show 2402 is in the set.
    constructor
    · -- Show that 0 ≤ 2402.
      norm_num
    · -- Show that sqrt (2402 + 99) - sqrt (2402) < 1.
      have h4 : sqrt ((2402 : ℝ) + 99) - sqrt (2402 : ℝ) < 1 := by 
        have h5 : sqrt ((2402 : ℝ) + (99 : ℝ)) = sqrt (2501 : ℝ) := by 
          norm_num
        rw [h5] at *
        have h6 : sqrt (2501 : ℝ) < 1 + sqrt (2402 : ℝ) := by 
          nlinarith [Real.sqrt_nonneg (2501 : ℝ), Real.sqrt_nonneg (2402 : ℝ), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2501 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2402 : ℝ) by norm_num), 
          sq_nonneg ((sqrt (2501 : ℝ) - (1 + sqrt (2402 : ℝ)) : ℝ)), 
          sq_nonneg ((sqrt (2402 : ℝ) - 49 : ℝ)), 
          Real.sqrt_nonneg (49 : ℝ), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (49 : ℝ) by norm_num)
          ]
        linarith
      simpa using h4
  · -- Show that no smaller natural number is in the set.
    intro n hn
    rcases hn with ⟨hn0, h1⟩
    by_contra h
    push_neg at h
    have h2 : n ≤ 2401 := by omega
    have h3 : (n : ℝ) ≤ (2401 : ℝ) := by exact_mod_cast h2
    have hk1 : sqrt ((n : ℝ) + 99) - sqrt ((n : ℝ)) ≥ 1 := by 
      have h5 : (n : ℝ) ≤ (2401 : ℝ) := h3
      have h8 : sqrt ((n : ℝ) + 99) ≥ sqrt ((n : ℝ)) + 1 := by 
        nlinarith [Real.sqrt_nonneg ((n : ℝ) + 99), Real.sqrt_nonneg ((n : ℝ)), sq_nonneg (sqrt ((n : ℝ) + 99) - (sqrt ((n : ℝ)) + 1)), Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) + 99 by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by linarith), sq_nonneg ((n : ℝ) - (2401 : ℝ)), Real.sqrt_nonneg (2401 + 99 : ℝ), Real.sqrt_nonneg (2401 : ℝ)]
      linarith [h8, Real.sqrt_nonneg ((n : ℝ) + 99), Real.sqrt_nonneg ((n : ℝ))]
    have h4 : sqrt ((n : ℝ) + 99) - sqrt ((n : ℝ)) < 1 := by 
      simpa using h1 
    linarith [hk1, h4, Real.sqrt_nonneg ((n : ℝ) + 99), Real.sqrt_nonneg ((n : ℝ))]