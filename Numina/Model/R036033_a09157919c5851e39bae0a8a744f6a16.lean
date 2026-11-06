import Mathlib

theorem number_theory_106044 (a b c p : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (hp : Nat.Prime p) (h : 73 * p ^ 2 + 6 = 9 * a ^ 2 + 17 * b ^ 2 + 17 * c ^ 2) :
    (a, b, c, p) = (1, 1, 4, 2) ∨ (a, b, c, p) = (1, 4, 1, 2) := by
  have h1 : p ≥ 2 := Nat.Prime.two_le hp
  have h2 : p ≤ 2 := by
    by_contra h3
    push_neg at h3
    have h3' : p ≥ 3 := by omega
    have h4 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
      have h5 : p % 2 = 1 := by
        by_contra h6
        push_neg at h6
        have : p % 2 = 0 := by omega
        have : ¬ Nat.Prime p := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega)
        contradiction
      have : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
        omega
      tauto
    have h5 : (p : ℕ) ^ 2 % 8 = 1 := by
      rcases h4 with (h4 | h4 | h4 | h4)
      · -- p % 8 = 1
        simp [Nat.pow_mod, h4, Nat.mul_mod, Nat.add_mod]
        all_goals omega
      · -- p % 8 = 3
        simp [Nat.pow_mod, h4, Nat.mul_mod, Nat.add_mod]
        all_goals omega
      · -- p % 8 = 5
        simp [Nat.pow_mod, h4, Nat.mul_mod, Nat.add_mod]
        all_goals omega
      · -- p % 8 = 7
        simp [Nat.pow_mod, h4, Nat.mul_mod, Nat.add_mod]
        all_goals omega
    have h6 : (a ^ 2 + b ^ 2 + c ^ 2) % 8 = 7 := by
      have h_mod : (73 * p ^ 2 + 6) % 8 = (9 * a ^ 2 + 17 * b ^ 2 + 17 * c ^ 2) % 8 := by
        omega
      simp [Nat.add_mod, Nat.mul_mod] at h_mod ⊢
      all_goals
      try omega
      all_goals try nlinarith
    have h7 : (a ^ 2 % 8 = 0 ∨ a ^ 2 % 8 = 1 ∨ a ^ 2 % 8 = 4) := by
      have h1 : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by
        omega
      rcases h1 with (h | h | h | h | h | h | h | h) <;> norm_num [Nat.pow_mod, h, Nat.mul_mod, Nat.add_mod] at *
      all_goals omega
    have h8 : (b ^ 2 % 8 = 0 ∨ b ^ 2 % 8 = 1 ∨ b ^ 2 % 8 = 4) := by
      have h1 : b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 4 ∨ b % 8 = 5 ∨ b % 8 = 6 ∨ b % 8 = 7 := by
        omega
      rcases h1 with (h | h | h | h | h | h | h | h) <;> norm_num [Nat.pow_mod, h, Nat.mul_mod, Nat.add_mod] at *
      all_goals omega
    have h9 : (c ^ 2 % 8 = 0 ∨ c ^ 2 % 8 = 1 ∨ c ^ 2 % 8 = 4) := by
      have h1 : c % 8 = 0 ∨ c % 8 = 1 ∨ c % 8 = 2 ∨ c % 8 = 3 ∨ c % 8 = 4 ∨ c % 8 = 5 ∨ c % 8 = 6 ∨ c % 8 = 7 := by
        omega
      rcases h1 with (h | h | h | h | h | h | h | h) <;> norm_num [Nat.pow_mod, h, Nat.mul_mod, Nat.add_mod] at *
      all_goals omega
    omega
  have hp2 : p = 2 := by
    linarith
  have eq1 : 73 * p ^ 2 + 6 = 298 := by
    norm_num [hp2]
  have eq2 : 9 * a ^ 2 + 17 * b ^ 2 + 17 * c ^ 2 = 298 := by
    linarith [h, eq1]
  have h3 : a ≤ 17 := by
    nlinarith
  have h4 : b ≤ 17 := by
    nlinarith
  have h5 : c ≤ 17 := by
    nlinarith
  interval_cases a <;> try { 
    omega 
  } <;> interval_cases b <;> try { 
    omega 
  } <;> interval_cases c 
  <;> norm_num [Prod.ext_iff] at *
  <;> try { 
    tauto 
  } 
  <;> try { 
    contradiction 
  }
  all_goals try { 
    contradiction 
  }
  all_goals try { 
    tauto 
  }