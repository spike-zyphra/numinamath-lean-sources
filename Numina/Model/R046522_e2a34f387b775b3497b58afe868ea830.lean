import Mathlib

theorem number_theory_262272 (n : ℕ) (h : ∃ k, n + 1 = k^3) :
    504 ∣ n * (n + 1) * (n + 2) := by
  rcases h with ⟨k, hk⟩
  have h1 : n * (n + 1) * (n + 2) % 8 = 0 := by
    have h2 : k ^ 3 % 8 = 0 ∨ k ^ 3 % 8 = 1 ∨ k ^ 3 % 8 = 3 ∨ k ^ 3 % 8 = 5 ∨ k ^ 3 % 8 = 7 := by
      have h3 : k % 8 = 0 ∨ k % 8 = 1 ∨ k % 8 = 2 ∨ k % 8 = 3 ∨ k % 8 = 4 ∨ k % 8 = 5 ∨ k % 8 = 6 ∨ k % 8 = 7 := by
        omega
      rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3) <;> simp [h3, Nat.pow_mod, Nat.mul_mod]
    have h8 : n * (n + 1) * (n + 2) % 8 = 0 := by
      rcases h2 with (h2 | h2 | h2 | h2 | h2)
      · -- if k^3 ≡ 0 [8], then n+1 ≡ 0 [8], so n+1 divisible by 8
        have h3' : (n + 1) % 8 = 0 := by
          omega
        simp [Nat.mul_mod, h3', Nat.add_mod, Nat.mul_mod]
      · -- if k^3 ≡ 1 [8], then n+1 ≡ 1 [8], so n ≡ 0 [8]
        have h3' : n % 8 = 0 := by
          omega
        simp [Nat.mul_mod, h3', Nat.add_mod, Nat.mul_mod]
      · -- if k^3 ≡ 3 [8], then n+1 ≡ 3 [8], so n ≡ 2 [8]
        have h3' : n % 8 = 2 := by
          omega
        simp [Nat.mul_mod, h3', Nat.add_mod, Nat.mul_mod]
      · -- if k^3 ≡ 5 [8], then n+1 ≡ 5 [8], so n ≡ 4 [8]
        have h3' : n % 8 = 4 := by
          omega
        simp [Nat.mul_mod, h3', Nat.add_mod, Nat.mul_mod]
      · -- if k^3 ≡ 7 [8], then n+1 ≡ 7 [8], so n ≡ 6 [8]
        have h3' : n % 8 = 6 := by
          omega
        simp [Nat.mul_mod, h3', Nat.add_mod, Nat.mul_mod]
    exact h8
  have h2 : n * (n + 1) * (n + 2) % 9 = 0 := by
    have h3 : k ^ 3 % 9 = 0 ∨ k ^ 3 % 9 = 1 ∨ k ^ 3 % 9 = 8 := by
      have h3 : k % 9 = 0 ∨ k % 9 = 1 ∨ k % 9 = 2 ∨ k % 9 = 3 ∨ k % 9 = 4 ∨ k % 9 = 5 ∨ k % 9 = 6 ∨ k % 9 = 7 ∨ k % 9 = 8 := by
        omega
      rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3) <;> simp [h3, Nat.pow_mod, Nat.mul_mod]
    have h8 : n * (n + 1) * (n + 2) % 9 = 0 := by
      rcases h3 with (h3 | h3 | h3)
      · -- if k^3 ≡ 0 [9], then n+1 ≡ 0 [9], so n+1 divisible by 9
        have h4' : (n + 1) % 9 = 0 := by
          omega
        simp [Nat.mul_mod, h4', Nat.add_mod, Nat.mul_mod]
      · -- if k^3 ≡ 1 [9], then n+1 ≡ 1 [9], so n ≡ 0 [9]
        have h4' : n % 9 = 0 := by
          omega
        simp [Nat.mul_mod, h4', Nat.add_mod, Nat.mul_mod]
      · -- if k^3 ≡ 8 [9], then n+1 ≡ 8 [9], so n ≡ 7 [9]
        have h4' : n % 9 = 7 := by
          omega
        simp [Nat.mul_mod, h4', Nat.add_mod, Nat.mul_mod]
    exact h8
  have h3 : n * (n + 1) * (n + 2) % 7 = 0 := by
    have h4 : k ^ 3 % 7 = 0 ∨ k ^ 3 % 7 = 1 ∨ k ^ 3 % 7 = 6 := by
      have h3 : k % 7 = 0 ∨ k % 7 = 1 ∨ k % 7 = 2 ∨ k % 7 = 3 ∨ k % 7 = 4 ∨ k % 7 = 5 ∨ k % 7 = 6 := by
        omega
      rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3) <;> simp [h3, Nat.pow_mod, Nat.mul_mod]
    have h8 : n * (n + 1) * (n + 2) % 7 = 0 := by
      rcases h4 with (h4 | h4 | h4)
      · -- if k^3 ≡ 0 [7], then n+1 ≡ 0 [7], so n+1 divisible by 7
        have h5' : (n + 1) % 7 = 0 := by
          omega
        simp [Nat.mul_mod, h5', Nat.add_mod, Nat.mul_mod]
      · -- if k^3 ≡ 1 [7], then n+1 ≡ 1 [7], so n ≡ 0 [7]
        have h5' : n % 7 = 0 := by
          omega
        simp [Nat.mul_mod, h5', Nat.add_mod, Nat.mul_mod]
      · -- if k^3 ≡ 6 [7], then n+1 ≡ 6 [7], so n ≡ 5 [7]
        have h5' : n % 7 = 5 := by
          omega
        simp [Nat.mul_mod, h5', Nat.add_mod, Nat.mul_mod]
    exact h8
  omega