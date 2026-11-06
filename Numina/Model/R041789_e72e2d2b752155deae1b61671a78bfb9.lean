import Mathlib

theorem algebra_129422 (n : ℤ) :
    IsSquare (n^2 + 8 * n + 44) ↔ n = 2 ∨ n = -10 := by 
  constructor
  · -- Forward: if $n^2 + 8 * n + 44$ is a perfect square, then n = 2 or n = -10
    intro h
    rcases h with ⟨k, hk⟩
    have h1 : k^2 - (n + 4) ^2 = 28 := by 
      nlinarith
    have h2 : (k - (n + 4)) * (k + (n + 4)) = 28 := by 
      ring_nf at h1 ⊢
      linarith
    have h3 : k - (n + 4) ∣ 28 := by
      use k + (n + 4)
      all_goals nlinarith [h2]
    have h4 : k - (n + 4) ≤ 28 := by 
      apply Int.le_of_dvd (by norm_num) h3
    have h5 : k - (n + 4) ≥ -28 := by 
      have h6 : - (k - (n + 4)) ∣ 28 := by 
        exact Int.neg_dvd.2 h3
      have h7 : - (k - (n + 4)) ≤ 28 := by 
        apply Int.le_of_dvd (by norm_num) h6
      linarith
    interval_cases h : k - (n + 4) <;> try { 
      omega 
    }
    all_goals 
      try { 
        have : n = 2 ∨ n = -10 := by 
          have : n ≤ 30 := by 
            nlinarith [sq_nonneg (k - 15), sq_nonneg (n + 15)]
          have : n ≥ -58 := by
            nlinarith [sq_nonneg (k + 15), sq_nonneg (n - 15)]
          interval_cases n <;> try { tauto }
        tauto 
      }
  · -- Backward: if n = 2 or n = -10, then $n^2 + 8 * n + 44$ is a perfect square
    rintro (h | h)
    · -- If n = 2
      rw [h]
      native_decide
    · -- If n = -10
      rw [h]
      native_decide