import Mathlib

theorem number_theory_232440 (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h : a^2 + b^2 + 1 = Nat.factorial c) :
    (a, b) = (1, 2) ∧ c = 3 ∨ (a, b) = (2, 1) ∧ c = 3 := by
  have h1 : c ≤ 3 := by
    by_contra h2
    push_neg at h2
    -- c > 3 implies c >= 4
    have h2' : c ≥ 4 := by omega
    -- c! divisible by 4 for c >= 4
    have h3 : 4 ∣ Nat.factorial c := by
      apply Nat.dvd_factorial
      all_goals omega
    -- Thus a^2 + b^2 + 1 divisible by 4
    have h4 : (a ^ 2 + b ^ 2 + 1) % 4 = 0 := by
      have h5 : 4 ∣ Nat.factorial c := h3
      have h6 : (Nat.factorial c) % 4 = 0 := by
        omega
      omega
    -- Analyze squares modulo 4. 
    -- a^2 + b^2 + 1 is never divisible by 4.
    have h5 : (a ^ 2 + b ^ 2 + 1) % 4 = 1 ∨ (a ^ 2 + b ^ 2 + 1) % 4 = 2 ∨ (a ^ 2 + b ^ 2 + 1) % 4 = 3 := by
      have h6 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
      have h7 : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by omega
      rcases h6 with (h6 | h6 | h6 | h6) <;> rcases h7 with (h7 | h7 | h7 | h7) <;> simp [Nat.add_mod, Nat.mul_mod, h6, h7, Nat.pow_two] 
    omega
  interval_cases c <;> try { 
    simp [Nat.factorial] at h 
    all_goals try { 
      have h2 : a ≤ 3 := by nlinarith
      have h3 : b ≤ 3 := by nlinarith
      interval_cases a <;> interval_cases b 
      all_goals norm_num [Prod.ext_iff] at h ⊢ 
    }
  }