import Mathlib

theorem number_theory_611076 (n : ℤ) : ⌊n / 2⌋ * ⌊(n + 1) / 2⌋ = ⌊n^2 / 4⌋ := by
  by_cases h : n % 2 = 0
  · -- Assume n is even.
    have h1 : ∃ k : ℤ, n = 2 * k := by 
      refine' ⟨n / 2, by 
        omega 
      ⟩ 
    rcases h1 with ⟨k, hk⟩ 
    have h2 : ⌊n / 2⌋ = k := by 
      rw [hk]
      simp [Int.floor_eq_iff, mul_comm]
    have h3 : ⌊(n + 1) / 2⌋ = k := by 
      rw [show n + 1 = 2 * k + 1 by linarith [hk]]
      simp [Int.floor_eq_iff]
      all_goals 
        try { 
          omega 
        } 
    have h4 : ⌊n^2 / 4⌋ = k^2 := by 
      have h_eq : n ^ 2 = 4 * k^2 := by 
        rw [hk]
        ring 
      rw [h_eq]
      simp [Int.floor_eq_iff, mul_comm]
      all_goals 
        try { 
          omega 
        }
    rw [h2, h3, h4]
    all_goals 
      nlinarith 
  · -- Case where n is odd. So n % 2 = 1
    have h2 : n % 2 = 1 := by 
      omega 
    have h1 : ∃ k : ℤ, n = 2 * k + 1 := by
      have h4 : n % 2 = 1 := h2
      refine' ⟨(n - 1) / 2, by 
        omega 
      ⟩ 
    rcases h1 with ⟨k, hk⟩ 
    have h2 : ⌊n / 2⌋ = k := by 
      rw [hk]
      simp [Int.floor_eq_iff, mul_comm]
      all_goals omega 
    have h3 : ⌊(n + 1) / 2⌋ = k + 1 := by 
      rw [show n + 1 = 2 * (k + 1) by linarith [hk]]
      simp [Int.floor_eq_iff, mul_comm]
      all_goals 
        try { 
          omega 
        } 
    have h4 : ⌊n^2 / 4⌋ = k^2 + k := by 
      have h_eq : n ^ 2 = 4 * (k^2 + k) + 1 := by 
        rw [hk]
        ring 
      rw [h_eq]
      simp [Int.floor_eq_iff, mul_comm]
      all_goals 
        try { 
          omega 
        }
    rw [h2, h3, h4]
    all_goals 
      nlinarith