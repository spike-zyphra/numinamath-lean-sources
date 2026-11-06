import Mathlib

theorem number_theory_260301 :
    IsLeast {n | n ≥ 1000 ∧ n < 10000 ∧ ∃ k, (n / 100) ^ 2 - (n % 100) ^ 2 = k ∧ k ∈ Finset.Icc 100 999 ∧
      ∃ m, k = m * 111} 2017 := by
  constructor
  · -- Show 2017 is in the set.
    constructor
    · norm_num
    constructor
    · norm_num
    use 111
    constructor
    · norm_num
    constructor
    · norm_num
    use 1
    all_goals norm_num
  · -- Show that no number less than 2017 is in the set.
    intro n hn
    rcases hn with ⟨h1, h2, k, h3, hk, m, h6⟩
    by_contra h
    push_neg at h
    have h7 : n < 2017 := by linarith
    rw [Finset.mem_Icc] at hk
    rcases hk with ⟨hk1, hk2⟩
    have h12 : k = m * 111 := by linarith
    have h13 : n / 100 ≤ 20 := by
      omega
    have h14 : n % 100 < 100 := by 
      omega
    have eq : (n / 100 : ℕ) ^ 2 - (n % 100 : ℕ) ^ 2 = m * 111 := by 
      linarith [h3, h12]
    have h15 : (n / 100 : ℕ) ≤ 20 := by 
      omega
    interval_cases h16 : (n / 100 : ℕ) <;> 
      try { 
        omega 
      } <;> 
        try { 
          interval_cases h17 : (n % 100 : ℕ) <;> omega 
        }