import Mathlib

theorem number_theory_223416 (n : ℕ) :
    24 ∣ 7^(2*n) - 5^(2*n) := by 
  have h1 : ∀ n : ℕ, 8 ∣ 7 ^ (2 * n) - 5 ^ (2 * n) := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      -- 7^(2*(n+1)) = 7^(2n+2) = 7^(2n) * 49
      -- 5^(2*(n+1)) = 5^(2n+2) = 5^(2n) * 25
      have h61 : 7 ^ (2 * (n + 1)) % 8 = 1 := by 
        have h62 : 7 ^ (2 * (n + 1)) = 7 ^ (2 * n) * 7 ^ 2 := by 
          ring_nf
        rw [h62]
        have h63 : 7 ^ 2 % 8 = 1 := by
          norm_num
        have h64 : 7 ^ (2 * n) % 8 = 1 := by 
          -- prove 7^(2n) % 8=1 by induction
          have h62 : ∀ n : ℕ, 7 ^ (2 * n) % 8 = 1 := by
            intro n 
            induction n with 
            | zero => 
              simp 
            | succ n ih => 
              have h61 : 7 ^ (2 * (n + 1)) % 8 = 1 := by
                have h63 : 7 ^ (2 * (n + 1)) = 7 ^ (2 * n) * 7 ^ 2 := by 
                  ring_nf
                rw [h63]
                simp [Nat.mul_mod, ih] 
              exact h61
          specialize h62 n 
          assumption 
        simp [Nat.mul_mod, h63, h64]
      have h71 : 5 ^ (2 * (n + 1)) % 8 = 1 := by 
        have h72 : 5 ^ (2 * (n + 1)) = 5 ^ (2 * n) * 5 ^ 2 := by 
          ring_nf
        rw [h72]
        have h73 : 5 ^ 2 % 8 = 1 := by
          norm_num
        have h74 : 5 ^ (2 * n) % 8 = 1 := by 
          -- prove 5^(2n) % 8=1 by induction
          have h71 : ∀ n : ℕ, 5 ^ (2 * n) % 8 = 1 := by
            intro n 
            induction n with 
            | zero => 
              simp 
            | succ n ih => 
              have h61 : 5 ^ (2 * (n + 1)) % 8 = 1 := by
                have h63 : 5 ^ (2 * (n + 1)) = 5 ^ (2 * n) * 5 ^ 2 := by 
                  ring_nf
                rw [h63]
                simp [Nat.mul_mod, ih] 
              exact h61
          specialize h71 n 
          assumption 
        simp [Nat.mul_mod, h73, h74]
      have h33 : (7 ^ (2 * (n + 1)) - 5 ^ (2 * (n + 1)) ) % 8 = 0 := by 
        omega 
      have h32 : 8 ∣ 7 ^ (2 * (n + 1)) - 5 ^ (2 * (n + 1)) := by 
        omega 
      exact h32 
  -- Prove divisibility by 3.
  have h2 : ∀ n : ℕ, 3 ∣ 7 ^ (2 * n) - 5 ^ (2 * n) := by
    intro n 
    induction n with
    | zero =>
      norm_num 
    | succ n ih => 
      have h61 : 7 ^ (2 * (n + 1)) % 3 = 1 := by 
        have h62 : 7 ^ (2 * (n + 1)) = 7 ^ (2 * n) * 7 ^ 2 := by 
          ring_nf
        rw [h62]
        have h63 : 7 ^ 2 % 3 = 1 := by 
          norm_num 
        have h64 : 7 ^ (2 * n) % 3 = 1 := by 
          -- prove 7^(2n) % 3=1 by induction
          have h62 : ∀ n : ℕ, 7 ^ (2 * n) % 3 = 1 := by
            intro n 
            induction n with 
            | zero => 
              simp 
            | succ n ih => 
              have h61 : 7 ^ (2 * (n + 1)) % 3 = 1 := by 
                have h63 : 7 ^ (2 * (n + 1)) = 7 ^ (2 * n) * 7 ^ 2 := by 
                  ring_nf
                rw [h63]
                simp [Nat.mul_mod, ih] 
              exact h61 
          specialize h62 n 
          assumption 
        simp [Nat.mul_mod, h63, h64] 
      have h71 : 5 ^ (2 * (n + 1)) % 3 = 1 := by 
        have h72 : 5 ^ (2 * (n + 1)) = 5 ^ (2 * n) * 5 ^ 2 := by 
          ring_nf
        rw [h72]
        have h73 : 5 ^ 2 % 3 = 1 := by 
          norm_num 
        have h74 : 5 ^ (2 * n) % 3 = 1 := by 
          -- prove 5^(2n) % 3=1 by induction
          have h71 : ∀ n : ℕ, 5 ^ (2 * n) % 3 = 1 := by
            intro n 
            induction n with 
            | zero => 
              simp 
            | succ n ih => 
              have h61 : 5 ^ (2 * (n + 1)) % 3 = 1 := by 
                have h63 : 5 ^ (2 * (n + 1)) = 5 ^ (2 * n) * 5 ^ 2 := by 
                  ring_nf
                rw [h63]
                simp [Nat.mul_mod, ih] 
              exact h61 
          specialize h71 n 
          assumption 
        simp [Nat.mul_mod, h73, h74] 
      have h33 : (7 ^ (2 * (n + 1)) - 5 ^ (2 * (n + 1)) ) % 3 = 0 := by 
        omega 
      have h32 : 3 ∣ 7 ^ (2 * (n + 1)) - 5 ^ (2 * (n + 1)) := by 
        omega 
      exact h32 
  -- Combine divisibility by 8 and 3 to get divisibility by 24.
  have h3 : ∀ n : ℕ, 24 ∣ 7 ^ (2 * n) - 5 ^ (2 * n) := by 
    intro n 
    have h1' : 8 ∣ 7 ^ (2 * n) - 5 ^ (2 * n) := h1 n
    have h2' : 3 ∣ 7 ^ (2 * n) - 5 ^ (2 * n) := h2 n
    omega 
  exact h3 n