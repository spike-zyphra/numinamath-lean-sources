import Mathlib

theorem number_theory_238185 (n : ℕ) :
    ¬ ∃ m, m^2 = 3^n + 2 * 17^n := by 
  rintro ⟨m, hm⟩
  have h1 : m ^ 2 % 8 = 0 ∨ m ^ 2 % 8 = 1 ∨ m ^ 2 % 8 = 4 := by
    have h2 : m % 8 = 0 ∨ m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 3 ∨ m % 8 = 4 ∨ m % 8 = 5 ∨ m % 8 = 6 ∨ m % 8 = 7 := by
      omega
    rcases h2 with (h | h | h | h | h | h | h | h) <;> simp [pow_two, Nat.mul_mod, h, Nat.add_mod, Nat.mul_mod]
    <;> omega
  have h2 : (3 ^ n + 2 * 17 ^ n) % 8 = 3 ∨ (3 ^ n + 2 * 17 ^ n) % 8 = 5 := by
    have h3 : ∀ n : ℕ, (3 ^ n : ℕ) % 8 = 1 ∨ (3 ^ n : ℕ) % 8 = 3 := by
      intro n 
      induction n with 
      | zero =>
        norm_num 
      | succ n ih =>
        have h4 : (3 ^ (n + 1) : ℕ) % 8 = (3 ^ n * 3) % 8 := by ring_nf 
        rw [h4] 
        rcases ih with (h | h) 
        · norm_num [Nat.mul_mod, h] 
        · norm_num [Nat.mul_mod, h] 
    have h4 : (3 ^ n : ℕ) % 8 = 1 ∨ (3 ^ n : ℕ) % 8 = 3 := h3 n 
    have h5 : (17 ^ n : ℕ) % 8 = 1 := by 
      have h4 : ∀ k : ℕ, (17 ^ k : ℕ) % 8 = 1 := by 
        intro k 
        induction k with 
        | zero =>
          norm_num 
        | succ k ihk => 
          simp [Nat.pow_succ, Nat.mul_mod, ihk] 
          <;> omega 
      specialize h4 n 
      simpa using h4 
    have h6 : (2 * 17 ^ n) % 8 = 2 := by 
      have h7 : (17 ^ n : ℕ) % 8 = 1 := h5 
      simp [Nat.mul_mod, h7] 
      <;> omega 
    omega
  have h3 : m ^ 2 % 8 = (3 ^ n + 2 * 17 ^ n) % 8 := by 
    omega 
  omega