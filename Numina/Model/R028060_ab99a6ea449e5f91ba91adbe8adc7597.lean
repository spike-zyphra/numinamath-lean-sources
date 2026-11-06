import Mathlib

theorem number_theory_131221 (n : ℕ) (h₀ : Odd n) (h₁ : ∃ k, n = k^2) :
    ¬∃ a b c d e : ℕ, Odd a ∧ Odd b ∧ Odd c ∧ Odd d ∧ Odd e ∧ n = a^2 + b^2 + c^2 + d^2 + e^2 := by 
  intro h
  rcases h₁ with ⟨k, hk⟩
  rcases h with ⟨a, b, c, d, e, ha, hb, hc, hd, he, h_eq⟩
  have h17 : k % 8 = 1 ∨ k % 8 = 3 ∨ k % 8 = 5 ∨ k % 8 = 7 := by
    have h16 : k % 2 = 1 := by 
      have h19 : k % 2 = 1 := by
        by_contra h
        push_neg at h
        have h22 : k % 2 = 0 := by
          omega
        have h23 : (k ^ 2) % 2 = 0 := by
          simp [Nat.pow_mod, h22]
        have h24 : (k ^ 2) % 2 = 1 := by 
          have h18 : Odd (k ^ 2) := by 
            rw [show k ^ 2 = n by linarith [hk]] at *
            exact h₀
          obtain ⟨m, hm⟩ := h18
          omega
        omega
      tauto
    have : k % 8 = 1 ∨ k % 8 = 3 ∨ k % 8 = 5 ∨ k % 8 = 7 := by 
      omega 
    assumption
  have h18 : k ^ 2 % 8 = 1 := by
    rcases h17 with (h | h | h | h)
    all_goals
      simp [Nat.pow_mod, h, Nat.mul_mod]
  have h9 : a ^ 2 % 8 = 1 := by
    have h10 : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by 
      have : a % 2 = 1 := by 
        obtain ⟨m, hm⟩ := ha
        omega 
      omega 
    rcases h10 with (h | h | h | h)
    all_goals 
      simp [Nat.pow_mod, h, Nat.mul_mod]
  have h11 : b ^ 2 % 8 = 1 := by
    have h12 : b % 8 = 1 ∨ b % 8 = 3 ∨ b % 8 = 5 ∨ b % 8 = 7 := by 
      have : b % 2 = 1 := by 
        obtain ⟨m, hm⟩ := hb
        omega 
      omega 
    rcases h12 with (h | h | h | h)
    all_goals 
      simp [Nat.pow_mod, h, Nat.mul_mod]
  have h13 : c ^ 2 % 8 = 1 := by
    have h14 : c % 8 = 1 ∨ c % 8 = 3 ∨ c % 8 = 5 ∨ c % 8 = 7 := by 
      have : c % 2 = 1 := by 
        obtain ⟨m, hm⟩ := hc
        omega 
      omega 
    rcases h14 with (h | h | h | h)
    all_goals 
      simp [Nat.pow_mod, h, Nat.mul_mod]
  have h15 : d ^ 2 % 8 = 1 := by
    have h16 : d % 8 = 1 ∨ d % 8 = 3 ∨ d % 8 = 5 ∨ d % 8 = 7 := by 
      have : d % 2 = 1 := by 
        obtain ⟨m, hm⟩ := hd
        omega 
      omega 
    rcases h16 with (h | h | h | h)
    all_goals 
      simp [Nat.pow_mod, h, Nat.mul_mod]
  have h17' : e ^ 2 % 8 = 1 := by
    have h18' : e % 8 = 1 ∨ e % 8 = 3 ∨ e % 8 = 5 ∨ e % 8 = 7 := by 
      have : e % 2 = 1 := by 
        obtain ⟨m, hm⟩ := he
        omega 
      omega 
    rcases h18' with (h | h | h | h)
    all_goals 
      simp [Nat.pow_mod, h, Nat.mul_mod]
  have h_eq1 : (k^2) % 8 = (a^2 + b^2 + c^2 + d^2 + e^2) % 8 := by
    omega
  omega