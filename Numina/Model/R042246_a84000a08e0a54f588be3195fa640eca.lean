import Mathlib

theorem number_theory_252654 (n : ℕ) :
    65^(6 * n) % 9 = 1 ∧
    65^(6 * n + 1) % 9 = 2 ∧
    65^(6 * n + 2) % 9 = 4 ∧
    65^(6 * n + 3) % 9 = 8 := by
  have h1 : 65 ^ (6 * n) % 9 = 1 := by
    have h2 : ∀ n : ℕ, (65 ^ (6 * n) : ℕ) % 9 = 1 := by
      intro n
      induction n with
      | zero =>
        norm_num
      | succ n ih =>
        simp [Nat.pow_add, Nat.pow_mul, Nat.mul_mod] at ih ⊢
        all_goals norm_num at ih ⊢
        all_goals omega
    specialize h2 n
    simpa using h2
  have h2 : 65 ^ (6 * n + 1) % 9 = 2 := by
    have h5 : 65 ^ (6 * n + 1) % 9 = 2 := by
      have h11 : ∀ n : ℕ, 65 ^ (6 * n + 1) % 9 = 2 := by
        intro n
        induction n with
        | zero =>
          norm_num
        | succ n ih =>
          simp [Nat.pow_add, Nat.pow_mul, Nat.mul_mod] at ih ⊢
          all_goals norm_num at ih ⊢
          all_goals omega
      specialize h11 n
      simpa using h11
    simpa using h5
  have h3 : 65 ^ (6 * n + 2) % 9 = 4 := by
    have h5 : 65 ^ (6 * n + 2) % 9 = 4 := by
      have h11 : ∀ n : ℕ, 65 ^ (6 * n + 2) % 9 = 4 := by
        intro n
        induction n with
        | zero =>
          norm_num
        | succ n ih =>
          simp [Nat.pow_add, Nat.pow_mul, Nat.mul_mod] at ih ⊢
          all_goals norm_num at ih ⊢
          all_goals omega
      specialize h11 n
      simpa using h11
    simpa using h5
  have h4 : 65 ^ (6 * n + 3) % 9 = 8 := by
    have h5 : 65 ^ (6 * n + 3) % 9 = 8 := by
      have h11 : ∀ n : ℕ, 65 ^ (6 * n + 3) % 9 = 8 := by
        intro n
        induction n with
        | zero =>
          norm_num
        | succ n ih =>
          simp [Nat.pow_add, Nat.pow_mul, Nat.mul_mod] at ih ⊢
          all_goals norm_num at ih ⊢
          all_goals omega
      specialize h11 n
      simpa using h11
    simpa using h5
  exact ⟨h1, h2, h3, h4⟩