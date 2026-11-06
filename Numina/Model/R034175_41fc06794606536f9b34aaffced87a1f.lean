import Mathlib

theorem number_theory_215864 {n : ℕ} (hn : n ≠ 0) :
    (n % 10) * 2016 = n ↔ n = 4032 ∨ n = 8064 ∨ n = 12096 ∨ n = 16128 := by 
  constructor
  · -- Forward direction: if (n % 10) * 2016 = n, then n must be one of {4032, 8064, 12096, 16128}.
    rintro h
    have h1 : n % 10 ≠ 0 := by
      by_contra h1
      have h2 : n % 10 = 0 := by omega
      rw [h2] at h
      have h3 : n = 0 := by
        omega 
      contradiction 
    have h2 : n % 10 > 0 := by 
      omega
    have h3 : n % 10 < 10 := by 
      omega 
    have h4 : n % 10 % 2 = 0 := by
      omega 
    have h6 : n % 10 = 2 ∨ n % 10 = 4 ∨ n % 10 = 6 ∨ n % 10 = 8 := by 
      omega 
    rcases h6 with h6 | h6 | h6 | h6
    · 
      have h7 : n = 4032 := by 
        omega 
      simp [h7]
    · 
      have h7 : n = 8064 := by 
        omega 
      simp [h7]
    · 
      have h7 : n = 12096 := by 
        omega 
      simp [h7]
    · 
      have h7 : n = 16128 := by 
        omega 
      simp [h7]
  · -- Backward direction: if n is one of {4032, 8064, 12096, 16128}, then (n % 10) * 2016 = n.
    rintro (rfl | rfl | rfl | rfl)
    · 
      norm_num 
    · 
      norm_num 
    · 
      norm_num 
    · 
      norm_num