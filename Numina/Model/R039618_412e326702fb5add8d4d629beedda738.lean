import Mathlib

theorem number_theory_82166 (n : ℕ) :
    10 ∣ 9^n + 8^n + 7^n + 6^n - 4^n - 3^n - 2^n - 1^n := by
  have h1 : ((9^n + 8^n + 7^n + 6^n - 4^n - 3^n - 2^n - 1^n ) : ℕ) % 10 = 0 := by
    have h3 : (9^n + 8^n + 7^n + 6^n - 4^n - 3^n - 2^n - 1^n : ℕ) % 2 = 0 := by
      have h4 : ∀ (n : ℕ), (9^n + 8^n + 7^n + 6^n : ℕ) % 2 = (4^n + 3^n + 2^n + 1^n : ℕ) % 2 := by
        intro n
        have h9 : (9^n : ℕ) % 2 = (1 : ℕ) := by
          have h9 : ∀ m : ℕ, (9 ^ m : ℕ) % 2 = (1 : ℕ) := by
            intro m
            induction m with
            | zero => simp
            | succ m ih => simp [Nat.pow_succ, Nat.mul_mod, ih]
          specialize h9 n
          simpa using h9
        have h8 : (8^n : ℕ) % 2 = (0 : ℕ) ^ n % 2 := by
          have h8 : ∀ m : ℕ, (8 ^ m : ℕ) % 2 = (0 : ℕ) ^ m % 2 := by
            intro m
            induction m with
            | zero => simp
            | succ m ih => simp [Nat.pow_succ, Nat.mul_mod, ih]
          specialize h8 n
          simpa using h8
        have h7 : (7^n : ℕ) % 2 = (1 : ℕ) := by
          have h7 : ∀ m : ℕ, (7 ^ m : ℕ) % 2 = (1 : ℕ) := by
            intro m
            induction m with
            | zero => simp
            | succ m ih => simp [Nat.pow_succ, Nat.mul_mod, ih]
          specialize h7 n
          simpa using h7
        have h6 : (6^n : ℕ) % 2 = (0 : ℕ) ^ n % 2 := by
          have h6 : ∀ m : ℕ, (6 ^ m : ℕ) % 2 = (0 : ℕ) ^ m % 2 := by
            intro m
            induction m with
            | zero => simp
            | succ m ih => simp [Nat.pow_succ, Nat.mul_mod, ih]
          specialize h6 n
          simpa using h6
        have h4n : (4^n : ℕ) % 2 = (0 : ℕ) ^ n % 2 := by
          have h4n : ∀ m : ℕ, (4 ^ m : ℕ) % 2 = (0 : ℕ) ^ m % 2 := by
            intro m
            induction m with
            | zero => simp
            | succ m ih => simp [Nat.pow_succ, Nat.mul_mod, ih]
          specialize h4n n
          simpa using h4n
        have h3n : (3^n : ℕ) % 2 = (1 : ℕ) := by
          have h3n : ∀ m : ℕ, (3 ^ m : ℕ) % 2 = (1 : ℕ) := by
            intro m
            induction m with
            | zero => simp
            | succ m ih => simp [Nat.pow_succ, Nat.mul_mod, ih]
          specialize h3n n
          simpa using h3n
        have h2n : (2^n : ℕ) % 2 = (0 : ℕ) ^ n % 2 := by
          have h2n : ∀ m : ℕ, (2 ^ m : ℕ) % 2 = (0 : ℕ) ^ m % 2 := by
            intro m
            induction m with
            | zero => simp
            | succ m ih => simp [Nat.pow_succ, Nat.mul_mod, ih]
          specialize h2n n
          simpa using h2n
        have h1n : (1^n : ℕ) % 2 = (1 : ℕ) := by
          have h1n : ∀ m : ℕ, (1 ^ m : ℕ) % 2 = (1 : ℕ) := by
            intro m
            induction m with
            | zero => simp
            | succ m ih => simp [Nat.pow_succ, Nat.mul_mod, ih]
          specialize h1n n
          simpa using h1n
        omega
      specialize h4 n
      omega
    have h8 : (9^n + 8^n + 7^n + 6^n - 4^n - 3^n - 2^n - 1^n : ℕ) % 5 = 0 := by
      have h4 : (9^n + 8^n + 7^n + 6^n : ℕ) % 5 = (4^n + 3^n + 2^n + 1^n : ℕ) % 5 := by
        have h9 : (9^n : ℕ) % 5 = (4^n : ℕ) % 5 := by
          have h9 : ∀ n : ℕ, (9 ^ n : ℕ) % 5 = (4 ^ n : ℕ) % 5 := by
            intro n
            induction n with
            | zero => simp
            | succ n ih =>
              simp [Nat.pow_succ, Nat.mul_mod, ih]
          specialize h9 n
          simpa using h9
        have h8 : (8^n : ℕ) % 5 = (3^n : ℕ) % 5 := by
          have h8 : ∀ n : ℕ, (8 ^ n : ℕ) % 5 = (3 ^ n : ℕ) % 5 := by
            intro n
            induction n with
            | zero => simp
            | succ n ih =>
              simp [Nat.pow_succ, Nat.mul_mod, ih]
          specialize h8 n
          simpa using h8
        have h7 : (7^n : ℕ) % 5 = (2^n : ℕ) % 5 := by
          have h7 : ∀ n : ℕ, (7 ^ n : ℕ) % 5 = (2 ^ n : ℕ) % 5 := by
            intro n
            induction n with
            | zero => simp
            | succ n ih =>
              simp [Nat.pow_succ, Nat.mul_mod, ih]
          specialize h7 n
          simpa using h7
        have h6 : (6^n : ℕ) % 5 = (1 : ℕ) := by
          have h6 : ∀ n : ℕ, (6 ^ n : ℕ) % 5 = (1 : ℕ) := by
            intro n
            induction n with
            | zero => simp
            | succ n ih =>
              simp [Nat.pow_succ, Nat.mul_mod, ih]
          specialize h6 n
          simpa using h6
        have h4n : (4^n : ℕ) % 5 = (4^n : ℕ) % 5 := by rfl
        have h3n : (3^n : ℕ) % 5 = (3^n : ℕ) % 5 := by rfl
        have h2n : (2^n : ℕ) % 5 = (2^n : ℕ) % 5 := by rfl
        have h1n : (1^n : ℕ) % 5 = (1 : ℕ) := by
          have h1n : ∀ n : ℕ, (1 ^ n : ℕ) % 5 = (1 : ℕ) := by
            intro n
            induction n with
            | zero => simp
            | succ n ih =>
              simp [Nat.pow_succ, Nat.mul_mod, ih]
          specialize h1n n
          simpa using h1n
        omega
      omega
    omega
  omega