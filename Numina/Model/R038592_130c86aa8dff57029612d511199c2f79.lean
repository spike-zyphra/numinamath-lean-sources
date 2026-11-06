import Mathlib

theorem number_theory_188946 (a : ℕ) (ha : Nat.Coprime a 561) :
    a ^ 560 ≡ 1 [MOD 561] := by
  norm_num [Nat.ModEq] at *
  have h1 : a ^ 560 % 3 = 1 := by
    have h1 : a % 3 = 1 ∨ a % 3 = 2 := by 
      have h3 : a % 3 = 1 ∨ a % 3 = 2 ∨ a % 3 = 0 := by 
        omega
      rcases h3 with (h | h | h)
      · left; omega
      · right; omega
      · 
        exfalso
        have h3 : a % 3 = 0 := by 
          omega
        have h4 : a.gcd 561 ≥ 3 := by
          have h5 : 3 ∣ a := by 
            omega
          have h6 : 3 ∣ 561 := by norm_num
          have h7 : 3 ∣ a.gcd 561 := by 
            exact Nat.dvd_gcd h5 h6
          have h8 : a.gcd 561 ≥ 3 := by 
            exact Nat.le_of_dvd (by linarith) h7
          linarith
        have h8 : a.gcd 561 = 1 := by 
          exact ha
        linarith
    rcases h1 with (h | h)
    · 
      have h2 : a % 3 = 1 := h
      norm_num [Nat.pow_mod, h2] at *
    · 
      have h2 : a % 3 = 2 := h
      norm_num [Nat.pow_mod, h2] at *
  have h2 : a ^ 560 % 11 = 1 := by
    have h1 : a % 11 = 1 ∨ a % 11 = 2 ∨ a % 11 = 3 ∨ a % 11 = 4 ∨ a % 11 = 5 ∨ a % 11 = 6 ∨ a % 11 = 7 ∨ a % 11 = 8 ∨ a % 11 = 9 ∨ a % 11 = 10 := by
      have h3 : a % 11 ≠ 0 := by
        by_contra h
        have h4 : a.gcd 561 ≥ 11 := by
          have h5 : 11 ∣ a := by 
            omega
          have h6 : 11 ∣ 561 := by norm_num
          have h7 : 11 ∣ a.gcd 561 := by 
            exact Nat.dvd_gcd h5 h6
          have h8 : a.gcd 561 ≥ 11 := by 
            exact Nat.le_of_dvd (by linarith) h7
          linarith
        have h4 : a.gcd 561 = 1 := by 
          exact ha
        linarith
      have h4 : a % 11 = 1 ∨ a % 11 = 2 ∨ a % 11 = 3 ∨ a % 11 = 4 ∨ a % 11 = 5 ∨ a % 11 = 6 ∨ a % 11 = 7 ∨ a % 11 = 8 ∨ a % 11 = 9 ∨ a % 11 = 10 := by 
        omega
      tauto
    rcases h1 with (h | h | h | h | h | h | h | h | h | h)
    all_goals 
      norm_num [Nat.pow_mod, h] at *
  have h3 : a ^ 560 % 17 = 1 := by
    have h1 : a % 17 = 1 ∨ a % 17 = 2 ∨ a % 17 = 3 ∨ a % 17 = 4 ∨ a % 17 = 5 ∨ a % 17 = 6 ∨ a % 17 = 7 ∨ a % 17 = 8 ∨ a % 17 = 9 ∨ a % 17 = 10 ∨ a % 17 = 11 ∨ a % 17 = 12 ∨ a % 17 = 13 ∨ a % 17 = 14 ∨ a % 17 = 15 ∨ a % 17 = 16 := by
      have h3 : a % 17 ≠ 0 := by
        by_contra h
        have h4 : a.gcd 561 ≥ 17 := by
          have h5 : 17 ∣ a := by 
            omega
          have h6 : 17 ∣ 561 := by norm_num
          have h7 : 17 ∣ a.gcd 561 := by 
            exact Nat.dvd_gcd h5 h6
          have h8 : a.gcd 561 ≥ 17 := by 
            exact Nat.le_of_dvd (by linarith) h7
          linarith
        have h4 : a.gcd 561 = 1 := by 
          exact ha
        linarith
      have h4 : a % 17 = 1 ∨ a % 17 = 2 ∨ a % 17 = 3 ∨ a % 17 = 4 ∨ a % 17 = 5 ∨ a % 17 = 6 ∨ a % 17 = 7 ∨ a % 17 = 8 ∨ a % 17 = 9 ∨ a % 17 = 10 ∨ a % 17 = 11 ∨ a % 17 = 12 ∨ a % 17 = 13 ∨ a % 17 = 14 ∨ a % 17 = 15 ∨ a % 17 = 16 := by 
        omega
      tauto
    rcases h1 with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h)
    all_goals 
      norm_num [Nat.pow_mod, h] at *
  omega