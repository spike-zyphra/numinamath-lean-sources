import Mathlib

theorem number_theory_109536 (n : ℕ) :
    ¬ ∃ m, m^2 = 3^n + 2 * 17^n := by
  rintro ⟨m, hm⟩
  have h1 : m ^ 2 % 8 = 0 ∨ m ^ 2 % 8 = 1 ∨ m ^ 2 % 8 = 4 := by
    have h2 : m % 8 = 0 ∨ m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 3 ∨ m % 8 = 4 ∨ m % 8 = 5 ∨ m % 8 = 6 ∨ m % 8 = 7 := by
      omega
    rcases h2 with (h | h | h | h | h | h | h | h) <;> simp [pow_two, Nat.add_mod, Nat.mul_mod, h, Nat.add_mod, Nat.mul_mod]

  -- Prove that $3^n + 2 \cdot 17^n \pmod 8 = 3$ or $5$.
  have h3 : (3^n + 2 * 17^n) % 8 = 3 ∨ (3^n + 2 * 17^n) % 8 = 5 := by
    have h4 : ∀ n : ℕ, (3^n + 2 * 17^n) % 8 = 3 ∨ (3^n + 2 * 17^n) % 8 = 5 := by
      intro n
      have h5 : ∀ n : ℕ, 3^n % 8 = 1 ∨ 3^n % 8 = 3 := by
        intro n
        induction n with
        | zero =>
          simp 
          all_goals omega 
        | succ n ih =>
          have h6 : (3 ^ (n + 1) ) % 8 = (3 ^ n * 3) % 8 := by 
            ring_nf 
          rw [h6]
          have h7 : (3^n * 3) % 8 = ( (3^n % 8) * (3 % 8) ) % 8 := by 
            simp [Nat.mul_mod]
          rw [h7]
          rcases ih with (h | h)
          · 
            simp [h, Nat.mul_mod, Nat.add_mod]
            <;> omega 
          · 
            simp [h, Nat.mul_mod, Nat.add_mod]
            <;> omega 
      -- proving that 17^n ≡ 1 (mod 8)
      have h6 : ∀ n : ℕ, (17^n) % 8 = 1 := by
        intro n 
        induction n with 
        | zero =>
          simp 
          all_goals omega 
        | succ n ih =>
          simp [Nat.pow_succ, Nat.mul_mod, ih]
          all_goals omega 
      -- Now using these facts to compute the desired expression.
      have h16 : (3^n ) % 8 = 1 ∨ (3^n ) % 8 = 3 := h5 n 
      have h17 : (17^n ) % 8 = 1 := h6 n
      omega 
    specialize h4 n 
    simpa using h4 
  -- Now, we have that m^2 % 8 is either 0,1,4 and the expression is either 3,5. This is a contradiction.
  have h4 : m ^ 2 % 8 = (3^n + 2 * 17^n) % 8 := by
    omega 
  omega 
  all_goals try { contradiction }
  all_goals try { omega }