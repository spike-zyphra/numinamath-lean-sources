import Mathlib

theorem number_theory_19013 : IsGreatest {d : ℕ | ∀ (m n : ℕ), 0 < m → 0 < n → m ≡ 6 [MOD 9] → n ≡ 0 [MOD 9] → d ∣ m * n} 27 := by 
  constructor
  · -- Show 27 is in the set
    show ∀ (m n : ℕ), 0 < m → 0 < n → m ≡ 6 [MOD 9] → n ≡ 0 [MOD 9] → 27 ∣ m * n
    intro m n hm hn h1 h2
    have h1' : m % 9 = 6 := h1
    have h2' : n % 9 = 0 := h2
    have h5 : m * n % 27 = 0 := by
      have h1 : m % 9 = 6 := h1'
      have h11 : m % 27 = 6 ∨ m % 27 = 15 ∨ m % 27 = 24 := by
        omega
      have h22 : n % 27 = 0 ∨ n % 27 = 9 ∨ n % 27 = 18 := by
        omega
      rcases h11 with (h | h | h)
      · 
        rcases h22 with (h' | h' | h')
        ·
          simp [Nat.mul_mod, h, h']
        ·
          simp [Nat.mul_mod, h, h']
        ·
          simp [Nat.mul_mod, h, h']
      · 
        rcases h22 with (h' | h' | h')
        ·
          simp [Nat.mul_mod, h, h']
        ·
          simp [Nat.mul_mod, h, h']
        ·
          simp [Nat.mul_mod, h, h']
      · 
        rcases h22 with (h' | h' | h')
        ·
          simp [Nat.mul_mod, h, h']
        ·
          simp [Nat.mul_mod, h, h']
        ·
          simp [Nat.mul_mod, h, h']
    exact Nat.dvd_of_mod_eq_zero h5
  · -- Show there is no larger element in the set
    intro d h
    have h1 := h 6 9 (by norm_num) (by norm_num) (by norm_num [Nat.ModEq]) (by norm_num [Nat.ModEq])
    have h2 := h 15 9 (by norm_num) (by norm_num) (by norm_num [Nat.ModEq]) (by norm_num [Nat.ModEq])
    have h3 : d ∣ 54 := by
      norm_num at h1 ⊢
      exact h1
    have h4 : d ∣ 135 := by
      norm_num at h2 ⊢
      exact h2
    have h5 : d ∣ 27 := by
      exact Nat.dvd_gcd h3 h4
    have h6 : d ≤ 27 := by 
      exact Nat.le_of_dvd (by linarith) h5
    linarith