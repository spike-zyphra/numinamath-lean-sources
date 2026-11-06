import Mathlib

def isWonderful (n : ℕ) := n > 0 ∧ (n + 1) > 0 ∧ (n + 2) > 0 ∧ ∃ m, m^2 = n + 1 ∧ n * (n + 1) * (n + 2) < 2017

theorem number_theory_316334 :
    IsGreatest {x | ∀ n, isWonderful n → x ∣ n * (n + 1) * (n + 2)} 60 := by
  constructor
  · -- Show 60 is in the set
    intro n hn
    rcases hn with ⟨hn1, hn2, hn3, ⟨m, hm1, hm2⟩⟩
    have h1 : n * (n + 1) * (n + 2) % 4 = 0 := by
      have h1 : m^2 = n + 1 := by
        nlinarith
      have h2 : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by
        omega
      rcases h2 with (h | h | h | h)
      · -- m % 4 = 0
        have h3 : m^2 % 4 = 0 := by
          simp [Nat.pow_mod, h]
        have h4 : (n + 1) % 4 = 0 := by
          omega
        have : (n * (n + 1) * (n + 2)) % 4 = 0 := by
          simp [Nat.mul_mod, h4, Nat.mul_mod]
        assumption
      · -- m % 4 = 1
        have h3 : m^2 % 4 = 1 := by
          simp [Nat.pow_mod, h]
        have h4 : (n) % 4 = 0 := by
          omega
        have : (n * (n + 1) * (n + 2)) % 4 = 0 := by
          simp [Nat.mul_mod, h4, Nat.mul_mod]
        assumption
      · -- m % 4 = 2
        have h3 : m^2 % 4 = 0 := by
          simp [Nat.pow_mod, h]
        have h4 : (n + 1) % 4 = 0 := by
          omega
        have : (n * (n + 1) * (n + 2)) % 4 = 0 := by
          simp [Nat.mul_mod, h4, Nat.mul_mod]
        assumption
      · -- m % 4 = 3
        have h3 : m^2 % 4 = 1 := by
          simp [Nat.pow_mod, h]
        have h4 : (n) % 4 = 0 := by
          omega
        have : (n * (n + 1) * (n + 2)) % 4 = 0 := by
          simp [Nat.mul_mod, h4, Nat.mul_mod]
        assumption
    have h3 : n * (n + 1) * (n + 2) % 3 = 0 := by
      have h1 : m^2 = n + 1 := by
        nlinarith
      have h2 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by
        omega
      rcases h2 with (h | h | h)
      · -- m % 3 = 0
        have h4 : m^2 % 3 = 0 := by
          simp [Nat.pow_mod, h]
        have h5 : (n + 1) % 3 = 0 := by
          omega
        have : n * (n + 1) * (n + 2) % 3 = 0 := by
          simp [Nat.mul_mod, h5]
        assumption
      · -- m % 3 = 1
        have h4 : m^2 % 3 = 1 := by
          simp [Nat.pow_mod, h]
        have h5 : (n) % 3 = 0 := by
          omega
        have : n * (n + 1) * (n + 2) % 3 = 0 := by
          simp [Nat.mul_mod, h5, Nat.mul_mod]
        assumption
      · -- m % 3 = 2
        have h4 : m^2 % 3 = 1 := by
          simp [Nat.pow_mod, h]
        have h5 : (n) % 3 = 0 := by
          omega
        have : n * (n + 1) * (n + 2) % 3 = 0 := by
          simp [Nat.mul_mod, h5, Nat.mul_mod]
        assumption
    have h4 : n * (n + 1) * (n + 2) % 5 = 0 := by
      have h1 : m^2 = n + 1 := by
        nlinarith
      have h2 : m % 5 = 0 ∨ m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by
        omega
      rcases h2 with (h | h | h | h | h)
      · -- m % 5 = 0
        have h3 : m^2 % 5 = 0 := by
          simp [Nat.pow_mod, h]
        have h4 : (n + 1) % 5 = 0 := by
          omega
        have : n * (n + 1) * (n + 2) % 5 = 0 := by
          simp [Nat.mul_mod, h4, Nat.mul_mod]
        assumption
      · -- m % 5 = 1
        have h3 : m^2 % 5 = 1 := by
          simp [Nat.pow_mod, h]
        have h4 : (n) % 5 = 0 := by
          omega
        have : n * (n + 1) * (n + 2) % 5 = 0 := by
          simp [Nat.mul_mod, h4, Nat.mul_mod]
        assumption
      · -- m % 5 = 2
        have h3 : m^2 % 5 = 4 := by
          simp [Nat.pow_mod, h]
        have h4 : (n + 2) % 5 = 0 := by
          omega
        have : n * (n + 1) * (n + 2) % 5 = 0 := by
          simp [Nat.mul_mod, h4, Nat.mul_mod]
        assumption
      · -- m % 5 = 3
        have h3 : m^2 % 5 = 4 := by
          simp [Nat.pow_mod, h]
        have h4 : (n + 2) % 5 = 0 := by
          omega
        have : n * (n + 1) * (n + 2) % 5 = 0 := by
          simp [Nat.mul_mod, h4, Nat.mul_mod]
        assumption
      · -- m % 5 = 4
        have h3 : m^2 % 5 = 1 := by
          simp [Nat.pow_mod, h]
        have h4 : (n) % 5 = 0 := by
          omega
        have : n * (n + 1) * (n + 2) % 5 = 0 := by
          simp [Nat.mul_mod, h4, Nat.mul_mod]
        assumption
    omega
  · -- Show 60 is the greatest such divisor
    intro x hx
    have h1 : ∀ n, isWonderful n → x ∣ n * (n + 1) * (n + 2) := hx
    -- 60 is the greatest common divisor
    have h2 : x ∣ 60 := by
      have h3 : isWonderful 3 := by
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        use 2
        all_goals
        norm_num
      have h4 : x ∣ 3 * (3 + 1) * (3 + 2) := h1 3 h3
      norm_num at h4 ⊢
      exact h4
    -- x divides 720
    have h3 : x ∣ 720 := by
      have h4 : isWonderful 8 := by
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        use 3
        all_goals
        norm_num
      have h5 : x ∣ 8 * (8 + 1) * (8 + 2) := h1 8 h4
      norm_num at h5 ⊢
      exact h5
    -- x divides GCD(60, 720) = 60
    have h4 : x ∣ 60 := by
      exact Nat.dvd_gcd h2 h3
    -- x ≤ 60
    have h5 : x ≤ 60 := by
      exact Nat.le_of_dvd (show 0 < 60 by norm_num) h4
    linarith