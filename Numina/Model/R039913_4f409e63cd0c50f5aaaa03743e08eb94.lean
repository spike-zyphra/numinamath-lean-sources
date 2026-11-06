import Mathlib

theorem number_theory_290841 (n : ℕ) (hn : Odd n) : 440 ∣ 12^n - (1^n + 4^n + 7^n) := by
  have h1 : n % 2 = 1 := by
    obtain ⟨k, hk⟩ := hn
    omega
  -- divisible by 8
  have h8 : (12 ^ n - (1 ^ n + 4 ^ n + 7 ^ n)) % 8 = 0 := by
    have h12 : ∀ n : ℕ, (12 ^ n : ℕ) % 8 = (4 ^ n) % 8 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => 
        simp [Nat.pow_succ, Nat.mul_mod] at ih ⊢
        all_goals omega
    -- 7^n ≡ (-1)^n ≡ -1 \pmod{8} (since n is odd)
    have h7 : ∀ n : ℕ, (7 ^ n : ℕ) % 8 = if n % 2 = 0 then 1 else 7 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => 
        simp [Nat.pow_succ, Nat.mul_mod] at ih ⊢
        split_ifs at ih ⊢ <;> try { 
          simp [ih] <;> omega
        }
        all_goals omega
    have h1' : n % 2 = 1 := h1
    have h7n : (7 ^ n : ℕ) % 8 = 7 := by
      specialize h7 n
      simp [h1'] at h7 ⊢
      all_goals omega
    have h12n : (12 ^ n) % 8 = (4 ^ n) % 8 := by
      apply h12 n
    have h1n : (1 ^ n) % 8 = 1 := by
      have : 1 ^ n = 1 := by
        induction n with
        | zero => simp
        | succ n ih => simp [Nat.pow_succ, ih]
      rw [this]
      all_goals norm_num
    -- compute each term mod 8
    omega
  -- divisible by 5
  have h5 : (12 ^ n - (1 ^ n + 4 ^ n + 7 ^ n)) % 5 = 0 := by
    have h12 : ∀ n : ℕ, (12 ^ n : ℕ) % 5 = (2 ^ n) % 5 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => 
        simp [Nat.pow_succ, Nat.mul_mod] at ih ⊢
        all_goals omega
    have h7 : ∀ n : ℕ, (7 ^ n : ℕ) % 5 = (2 ^ n) % 5 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => 
        simp [Nat.pow_succ, Nat.mul_mod] at ih ⊢
        all_goals omega
    have h12n : (12 ^ n) % 5 = (2 ^ n) % 5 := by
      apply h12 n
    have h7n : (7 ^ n) % 5 = (2 ^ n) % 5 := by
      apply h7 n
    have h1n : (1 ^ n) % 5 = 1 := by
      have : 1 ^ n = 1 := by
        induction n with
        | zero => simp
        | succ n ih => simp [Nat.pow_succ, ih]
      rw [this]
      all_goals norm_num
    -- 4^n ≡ -1 \pmod{5} (since n is odd)
    have h9 : (4 ^ n : ℕ) % 5 = 4 := by
      have h1' : n % 2 = 1 := h1
      have h9 : ∀ k : ℕ, (4 ^ (2 * k + 1 : ℕ)) % 5 = 4 := by
        intro k
        induction k with
        | zero => simp
        | succ k ih => 
          simp [Nat.pow_succ, Nat.pow_mul, Nat.mul_mod] at ih ⊢
          all_goals omega
      have : n = 2 * (n / 2) + 1 := by omega
      rw [this]
      specialize h9 (n / 2)
      omega
    -- compute each term mod 5
    omega
  -- divisible by 11
  have h11 : (12 ^ n - (1 ^ n + 4 ^ n + 7 ^ n)) % 11 = 0 := by
    have h12 : ∀ n : ℕ, (12 ^ n : ℕ) % 11 = (1 ^ n) % 11 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => 
        simp [Nat.pow_succ, Nat.mul_mod] at ih ⊢
        all_goals omega
    have h1n : (1 ^ n : ℕ) % 11 = 1 := by
      have : 1 ^ n = 1 := by
        induction n with
        | zero => simp
        | succ n ih => simp [Nat.pow_succ, ih]
      rw [this]
      all_goals norm_num
    have h12n : (12 ^ n) % 11 = 1 := by
      specialize h12 n
      rw [h1n] at h12
      omega
    -- 4^n + 7^n ≡ 0 \pmod{11} (since n is odd)
    have h9 : (4 ^ n + 7 ^ n) % 11 = 0 := by
      have h1' : n % 2 = 1 := h1
      have h10 : ∀ k : ℕ, (4 ^ (2 * k + 1 : ℕ) + 7 ^ (2 * k + 1 : ℕ)) % 11 = 0 := by
        intro k
        induction k with
        | zero => 
          norm_num
        | succ k ih => 
          simp [Nat.pow_succ, Nat.pow_mul, Nat.add_mod, Nat.mul_mod] at ih ⊢
          all_goals omega
      have : n = 2 * (n / 2) + 1 := by omega
      rw [this]
      specialize h10 (n / 2)
      omega
    -- compute each term mod 11
    omega
  -- Therefore, it is divisible by 8·5·11 = 440.
  omega