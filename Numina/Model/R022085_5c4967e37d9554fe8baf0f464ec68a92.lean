import Mathlib

theorem number_theory_232662 (n : ℕ) (hn : Odd n) : 64 ∣ n^4 + 7 * (7 + 2 * n^2) := by
  rcases hn with ⟨k, hk⟩
  have h_eq : n = 2 * k + 1 := by linarith
  have h1 : n^4 + 7 * (7 + 2 * n^2) = 16 * (k ^ 2 + k + 2) ^ 2 := by
    rw [h_eq]
    ring_nf
  have h2 : n^4 + 7 * (7 + 2 * n^2) = 16 * (k ^ 2 + k + 2) ^ 2 := h1
  -- Show 16 * (k ^ 2 + k + 2) ^ 2 is divisible by 64
  have h4 : (16 * (k ^ 2 + k + 2) ^ 2 : ℕ) % 64 = 0 := by
    have h9 : (k ^ 2 + k + 2) % 2 = 0 := by 
      have h10 : k % 2 = 0 ∨ k % 2 = 1 := by omega
      rcases h10 with (h10 | h10)
      · -- k is even.
        simp [Nat.add_mod, Nat.mul_mod, h10, pow_two]
        <;> omega
      · -- k is odd.
        simp [Nat.add_mod, Nat.mul_mod, h10, pow_two]
        all_goals omega
    -- Therefore (k^2 + k + 2) is even. Then its square is divisible by 4.
    have h7 : (k ^ 2 + k + 2) ^ 2 % 4 = 0 := by 
      have h8 : (k ^ 2 + k + 2) % 2 = 0 := h9 
      have h9 : (k ^ 2 + k + 2) % 4 = 0 ∨ (k ^ 2 + k + 2) % 4 = 2 := by 
        have h10 : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
        rcases h10 with (h10 | h10 | h10 | h10)
        · -- k ≡ 0 mod 4.
          simp [Nat.add_mod, Nat.mul_mod, h10, pow_two]
          all_goals omega
        · -- k ≡ 1 mod 4.
          simp [Nat.add_mod, Nat.mul_mod, h10, pow_two]
          all_goals omega
        · -- k ≡ 2 mod 4.
          simp [Nat.add_mod, Nat.mul_mod, h10, pow_two]
          all_goals omega
        · -- k ≡ 3 mod 4.
          simp [Nat.add_mod, Nat.mul_mod, h10, pow_two]
          all_goals omega
      rcases h9 with (h9 | h9)
      · -- Case where the value is 0 mod 4.
        simp [Nat.pow_mod, h9]
        all_goals omega
      · -- Case where the value is 2 mod 4.
        simp [Nat.pow_mod, h9]
        all_goals omega
    have h8 : (16 * (k ^ 2 + k + 2 : ℕ) ^ 2 : ℕ) % 64 = 0 := by
      have h11 : (k ^ 2 + k + 2 : ℕ) ^ 2 % 4 = 0 := h7
      have h12 : (k ^ 2 + k + 2 : ℕ) ^ 2 = 4 * ((k ^ 2 + k + 2 : ℕ) ^ 2 / 4) := by 
        omega
      rw [h12]
      ring_nf
      all_goals omega
    assumption
  rw [h2]
  omega
  all_goals omega