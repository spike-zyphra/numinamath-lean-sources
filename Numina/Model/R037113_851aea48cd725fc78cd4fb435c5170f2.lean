import Mathlib

theorem number_theory_4964 (m n k : ℕ)
    (h1 : 6 ∣ (m + n + k))
    (h2 : 36 ∣ (m ^ 2 + n ^ 2 + k ^ 2)) :
    8 ∣ (m ^ 3 + n ^ 3 + k ^ 3) := by 
  have h1a : (m ^ 2 + n ^ 2 + k ^ 2) % 4 = 0 := by 
    omega
  have hm : m % 2 = 0 := by 
    by_cases hm1 : m % 2 = 1 
    · -- Assume m is odd. Then m % 2 = 1.
      have hm11 : m % 2 = 1 := hm1
      have h3 : m ^ 2 % 4 = 1 := by
        have : m % 4 = 1 ∨ m % 4 = 3 := by
          omega 
        rcases this with (h4 | h4) 
        · -- m % 4 = 1 
          simp [Nat.pow_mod, h4] 
        · -- m % 4 = 3 
          simp [Nat.pow_mod, h4] 
      have h5 : (n ^ 2 + k ^ 2) % 4 = 3 := by 
        omega 
      have h5a : (n ^ 2 % 4 = 0 ∨ n ^ 2 % 4 = 1) := by
        have h5a : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by 
          omega 
        rcases h5a with (h | h | h | h) <;> simp [Nat.pow_mod, h] 
      have h5b : (k ^ 2 % 4 = 0 ∨ k ^ 2 % 4 = 1) := by 
        have h5a : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by 
          omega 
        rcases h5a with (h | h | h | h) <;> simp [Nat.pow_mod, h] 
      omega 
    · -- Assume m is not odd, so m % 2 = 0.
      omega 
  have hn : n % 2 = 0 := by 
    by_cases hn1 : n % 2 = 1 
    · -- Assume n is odd. Then n % 2 = 1.
      have hn11 : n % 2 = 1 := hn1 
      have h3 : n ^ 2 % 4 = 1 := by 
        have : n % 4 = 1 ∨ n % 4 = 3 := by
          omega 
        rcases this with (h4 | h4)
        · -- n % 4 = 1 
          simp [Nat.pow_mod, h4] 
        · -- n % 4 = 3 
          simp [Nat.pow_mod, h4] 
      have h5 : (m ^ 2 + k ^ 2) % 4 = 3 := by 
        omega 
      have h5a : (m ^ 2 % 4 = 0 ∨ m ^ 2 % 4 = 1) := by 
        have h5a : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by 
          omega 
        rcases h5a with (h | h | h | h) <;> simp [Nat.pow_mod, h] 
      have h5b : (k ^ 2 % 4 = 0 ∨ k ^ 2 % 4 = 1) := by 
        have h5a : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by 
          omega 
        rcases h5a with (h | h | h | h) <;> simp [Nat.pow_mod, h] 
      omega 
    · -- Assume n is not odd, so n % 2 = 0.
      omega 
  have hk : k % 2 = 0 := by 
    by_cases hk1 : k % 2 = 1 
    · -- Assume k is odd. Then k % 2 = 1.
      have hk11 : k % 2 = 1 := hk1 
      have h3 : k ^ 2 % 4 = 1 := by
        have : k % 4 = 1 ∨ k % 4 = 3 := by
          omega 
        rcases this with (h4 | h4) 
        · -- k % 4 = 1 
          simp [Nat.pow_mod, h4] 
        · -- k % 4 = 3 
          simp [Nat.pow_mod, h4] 
      have h5 : (m ^ 2 + n ^ 2) % 4 = 3 := by 
        omega 
      have h5a : (m ^ 2 % 4 = 0 ∨ m ^ 2 % 4 = 1) := by 
        have h5a : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by 
          omega 
        rcases h5a with (h | h | h | h) <;> simp [Nat.pow_mod, h] 
      have h5b : (n ^ 2 % 4 = 0 ∨ n ^ 2 % 4 = 1) := by 
        have h5a : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by 
          omega 
        rcases h5a with (h | h | h | h) <;> simp [Nat.pow_mod, h] 
      omega 
    · -- Assume k is not odd, so k % 2 = 0.
      omega 
  have h4a1 : ∃ a : ℕ, m = 2 * a := by 
    refine' ⟨m / 2, by omega⟩ 
  have h4a2 : ∃ b : ℕ, n = 2 * b := by 
    refine' ⟨n / 2, by omega⟩ 
  have h4a3 : ∃ c : ℕ, k = 2 * c := by 
    refine' ⟨k / 2, by omega⟩ 
  rcases h4a1 with ⟨a, ha⟩ 
  rcases h4a2 with ⟨b, hb⟩ 
  rcases h4a3 with ⟨c, hc⟩ 
  rw [ha, hb, hc]
  ring_nf 
  all_goals 
    omega