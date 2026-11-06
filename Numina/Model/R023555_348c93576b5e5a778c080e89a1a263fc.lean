import Mathlib

theorem number_theory_134322 :
    IsLeast {d | ∃ m n : ℕ, m > 0 ∧ n > 0 ∧ Nat.Coprime m n ∧ d.Prime ∧ d > 7 ∧ d ∣ m + 2024 * n ∧ d ∣ n + 2024 * m} 17 := by 
  constructor 
  · -- Show 17 is achievable via m = 1, n = 16
    use 1, 16
    all_goals norm_num 
  · -- Show no prime smaller than 17 is in the set
    intro d hd
    rcases hd with ⟨m, n, hm, hn, h_coprime, h_prime, h_gt, h1, h2⟩
    by_contra h 
    push_neg at h 
    have h3 : d < 17 := h 
    have h4 : d < 17 := h 
    have h5 : d > 7 := h_gt 
    have h6 : d = 11 ∨ d = 13 := by
      interval_cases d <;> norm_num at h_prime h_gt ⊢
      <;> tauto 
    rcases h6 with (h7 | h7)
    · -- Assume d = 11 
      rw [h7] at h1 h2 
      have h7 : m % 11 = 0 := by
        omega 
      have h8 : n % 11 = 0 := by 
        omega 
      have h9 : ¬ Nat.Coprime m n := by 
        simp [Nat.coprime_iff_gcd_eq_one] at h_coprime ⊢ 
        have h11 : m % 11 = 0 := h7
        have h12 : n % 11 = 0 := h8
        have h11' : 11 ∣ m := by omega
        have h12' : 11 ∣ n := by omega 
        have h13 : Nat.gcd m n ≥ 11 := by
          have h14 : 11 ∣ Nat.gcd m n := by 
            exact Nat.dvd_gcd h11' h12'
          have h15 : Nat.gcd m n ≥ 11 := by 
            omega 
          omega 
        have h14 : Nat.gcd m n = 1 := by 
          exact Nat.coprime_iff_gcd_eq_one.mp h_coprime 
        omega 
      contradiction 
    · -- Assume d = 13 
      rw [h7] at h1 h2 
      have h3 : m % 13 = 0 := by
        omega 
      have h4 : n % 13 = 0 := by 
        omega 
      have h5 : ¬ Nat.Coprime m n := by
        simp [Nat.coprime_iff_gcd_eq_one] at h_coprime ⊢
        have h11 : m % 13 = 0 := h3
        have h12 : n % 13 = 0 := h4
        have h11' : 13 ∣ m := by omega 
        have h12' : 13 ∣ n := by omega 
        have h13 : Nat.gcd m n ≥ 13 := by
          have h14 : 13 ∣ Nat.gcd m n := by 
            exact Nat.dvd_gcd h11' h12'
          have h15 : Nat.gcd m n ≥ 13 := by 
            omega 
          omega 
        have h14 : Nat.gcd m n = 1 := by 
          exact Nat.coprime_iff_gcd_eq_one.mp h_coprime 
        omega 
      contradiction