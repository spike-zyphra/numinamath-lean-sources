import Mathlib

theorem algebra_297363 {m n : ℤ} (h : 2*m^2+n^2+3*m+n-1=0) :
    (m=-1 ∧ n=1) ∨ (m=-1 ∧ n=-2) := by 
  have h1 : m = -1 ∨ m = 0 := by
    have hdisc : 8*m^2 + 12*m -5 ≤ 0 := by
      nlinarith [sq_nonneg (n + 1), sq_nonneg (m + 1 : ℤ), sq_nonneg (4*n + 1 : ℤ), sq_nonneg (m + 1 : ℤ), sq_nonneg (m - 0 : ℤ), sq_nonneg (n + 2 : ℤ), sq_nonneg (m + 2 : ℤ)]
    have h2 : m ≥ -1 := by 
      nlinarith [sq_nonneg (m + 1 : ℤ)]
    have h3 : m ≤ 0 := by 
      nlinarith [sq_nonneg (m + 1 : ℤ), sq_nonneg (m - 0 : ℤ)]
    interval_cases m <;> omega 
  rcases h1 with (hm | hm)
  · -- Case m = -1
    have h_eq : n^2 + n - 2 = 0 := by
      rw [hm] at h
      nlinarith 
    have : (n - 1) * (n + 2) = 0 := by nlinarith 
    cases' (mul_eq_zero.1 this) with hn1 hn2
    · -- Case n - 1 = 0
      have hn : n = 1 := by linarith 
      left 
      exact ⟨hm, hn⟩ 
    · -- Case n + 2 = 0
      have hn : n = -2 := by linarith 
      right 
      exact ⟨hm, hn⟩ 
  · -- Case m = 0
    have h_eq : n^2 + n - 1 = 0 := by
      rw [hm] at h 
      nlinarith
    exfalso 
    have h7 : n ≤ 1 := by
      nlinarith [sq_nonneg (n + (1 : ℤ)/2), sq_nonneg (n + 1), sq_nonneg (n - 0), sq_nonneg (n - 1), sq_nonneg (n + 2), sq_nonneg ((n + 1 : ℤ)), sq_nonneg ((n - 1 : ℤ))]
    have h8 : n ≥ -2 := by
      nlinarith [sq_nonneg (n + (1 : ℤ)/2), sq_nonneg (n + 1), sq_nonneg (n - 0), sq_nonneg (n - 1), sq_nonneg (n + 2), sq_nonneg ((n + 1 : ℤ)), sq_nonneg ((n - 1 : ℤ))]
    interval_cases n <;> omega 
    all_goals 
      try { 
        omega 
      }
      <;> 
      try { 
        nlinarith 
      }
      <;> 
      try { 
        nlinarith [sq_nonneg (n + 1 : ℤ), sq_nonneg (n - 1 : ℤ)]
      }
      <;> 
      try { 
        nlinarith [sq_nonneg (n : ℤ)]
      }