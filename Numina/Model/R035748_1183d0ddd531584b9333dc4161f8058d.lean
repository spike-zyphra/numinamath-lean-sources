import Mathlib

theorem algebra_120208 (n : ℕ) :
    Nat.gcd (4^n * 5^(2 * n + 4) - 1) (4^(n + 4) * 5^(2 * n) - 1) ≠ 1 := by
  have h1 : 3 ∣ (4^n * 5^(2 * n + 4) - 1 : ℕ) := by
    have h2 : (4^n * 5^(2 * n + 4) : ℕ) % 3 = 1 := by
      have h4 : ∀ (n : ℕ), (4^n * 5^(2 * n + 4) : ℕ) % 3 = 1 := by
        intro n
        have h5 : (4^n * 5^(2 * n + 4) : ℕ) % 3 = 1 := by
          have h12 : (4 : ℕ) % 3 = 1 := by norm_num
          have h13 : (5 ^ 2) % 3 = 1 := by norm_num
          have h14 : (5 ^ 4) % 3 = 1 := by norm_num
          have h15 : (4^n : ℕ) % 3 = 1 := by
            have h16 : ∀ (k : ℕ), (4^k : ℕ) % 3 = 1 := by
              intro k
              induction k with
              | zero => 
                norm_num
              | succ k ih =>
                simp [Nat.pow_succ] at ih ⊢
                omega
            specialize h16 n
            simpa using h16
          have h18 : (5 ^ (2 * n + 4) : ℕ) % 3 = 1 := by
            have h19 : ∀ (k : ℕ), (5 ^ (2 * k + 4) : ℕ) % 3 = 1 := by
              intro k
              induction k with
              | zero => 
                norm_num
              | succ k ih =>
                have h24 : (5 ^ (2 * (k + 1) + 4) : ℕ) = (5 ^ (2 * k + 4) : ℕ) * (5 ^ 2 : ℕ) := by 
                  ring_nf
                rw [h24]
                simp [Nat.mul_mod, ih] at *
            specialize h19 n
            simpa using h19
          have h19 : (4^n * 5^(2 * n + 4) : ℕ) % 3 = 1 := by
            simp [Nat.mul_mod, h15, h18]
          exact h19
        exact h5
      exact h4 n
    have h3 : (4^n * 5^(2 * n + 4) : ℕ) % 3 = 1 := h2
    have h4 : (4^n * 5^(2 * n + 4) - 1 : ℕ) % 3 = 0 := by
      have h8 : (4^n * 5^(2 * n + 4) : ℕ) % 3 = 1 := h3
      have h9 : (4^n * 5^(2 * n + 4) : ℕ) ≥ 1 := by
        have h100 : (4^n : ℕ) ≥ 1 := by
          apply Nat.one_le_pow
          all_goals norm_num
        have h110 : (5 ^ (2 * n + 4) : ℕ) ≥ 1 := by
          apply Nat.one_le_pow
          all_goals omega
        have h120 : (4^n * 5 ^ (2 * n + 4) : ℕ) ≥ 1 := by 
          nlinarith [show 0 ≤ (4 : ℕ) by norm_num, show 0 ≤ (5 : ℕ) by norm_num]
        linarith
      have h10 : (4^n * 5^(2 * n + 4) : ℕ) = (4^n * 5^(2 * n + 4) - 1 : ℕ) + 1 := by 
        omega
      omega
    omega
  have h11 : 3 ∣ (4^(n + 4) * 5^(2 * n) - 1 : ℕ) := by
    have h2 : (4^(n + 4) * 5^(2 * n) : ℕ) % 3 = 1 := by
      have h4 : ∀ (n : ℕ), (4 ^ (n + 4) * 5 ^ (2 * n) : ℕ) % 3 = 1 := by
        intro n
        have h5 : (4 ^ (n + 4) * 5 ^ (2 * n) : ℕ) % 3 = 1 := by
          have h12 : (4 : ℕ) % 3 = 1 := by norm_num
          have h13 : (5 ^ 2) % 3 = 1 := by norm_num
          have h15 : (4^(n + 4) : ℕ) % 3 = 1 := by
            have h16 : (4^(n + 4) : ℕ) % 3 = 1 := by
              have h7 : ∀ (k : ℕ), (4^(k + 4) : ℕ) % 3 = 1 := by
                intro k
                induction k with
                | zero => 
                  norm_num
                | succ k ih =>
                  have h9 : (4 ^ ((k + 1) + 4) : ℕ) = (4 ^ (k + 4) : ℕ) * (4 ^ 1 : ℕ) := by 
                    ring_nf
                  rw [h9]
                  simp [Nat.mul_mod, ih] at *
              specialize h7 n
              simpa using h7
            exact h16
          have h18 : (5 ^ (2 * n) : ℕ) % 3 = 1 := by
            have h19 : ∀ (k : ℕ), (5 ^ (2 * k) : ℕ) % 3 = 1 := by
              intro k
              induction k with
              | zero => 
                norm_num
              | succ k ih =>
                have h24 : (5 ^ (2 * (k + 1)) : ℕ) = (5 ^ (2 * k) : ℕ) * (5 ^ 2 : ℕ) := by 
                  ring_nf
                rw [h24]
                simp [Nat.mul_mod, ih] at *
            specialize h19 n
            simpa using h19
          have h19 : (4 ^ (n + 4) * 5 ^ (2 * n) : ℕ) % 3 = 1 := by
            simp [Nat.mul_mod, h15, h18]
          exact h19
        exact h5
      exact h4 n
    have h3 : (4^(n + 4) * 5^(2 * n) : ℕ) % 3 = 1 := h2
    have h4 : (4^(n + 4) * 5^(2 * n) - 1 : ℕ) % 3 = 0 := by
      have h8 : (4^(n + 4) * 5^(2 * n) : ℕ) % 3 = 1 := h3
      have h9 : (4^(n + 4) * 5^(2 * n) : ℕ) ≥ 1 := by
        have h100 : (4^(n + 4) : ℕ) ≥ 1 := by
          apply Nat.one_le_pow
          all_goals omega
        have h110 : (5 ^ (2 * n) : ℕ) ≥ 1 := by
          apply Nat.one_le_pow
          all_goals omega
        have h120 : (4^(n + 4) * 5 ^ (2 * n) : ℕ) ≥ 1 := by
          nlinarith [show 0 ≤ (4 : ℕ) by norm_num, show 0 ≤ (5 : ℕ) by norm_num]
        linarith
      have h10 : (4^(n + 4) * 5^(2 * n) : ℕ) = (4^(n + 4) * 5^(2 * n) - 1 : ℕ) + 1 := by
        omega
      omega
    omega
  have h12 : 3 ∣ Nat.gcd (4^n * 5^(2 * n + 4) - 1) (4^(n + 4) * 5^(2 * n) - 1) := by
    apply Nat.dvd_gcd
    exact h1
    exact h11
  intro h
  have h13 : Nat.gcd (4^n * 5^(2 * n + 4) - 1) (4^(n + 4) * 5^(2 * n) - 1) = 1 := by
    omega
  have h14 : 3 ∣ 1 := by
    rw [show Nat.gcd (4^n * 5^(2 * n + 4) - 1) (4^(n + 4) * 5^(2 * n) - 1) = 1 by linarith [h13]] at h12
    exact h12
  omega