import Mathlib

theorem number_theory_4788 (n : ℕ) (h₀ : Odd n) (h₁ : ¬ 3 ∣ n) :
    n^2 ≡ 1 [MOD 24] := by
  have h2 : n % 24 = 1 ∨ n % 24 = 5 ∨ n % 24 = 7 ∨ n % 24 = 11 ∨ n % 24 = 13 ∨ n % 24 = 17 ∨ n % 24 = 19 ∨ n % 24 = 23 := by
    rcases h₀ with ⟨k, hk⟩
    -- n is odd, so n = 2k + 1
    -- From the given that n ≡ 0 mod 3, we have to prove it in a different way
    have h3 : n % 3 ≠ 0 := by
      intro h
      have h4 : 3 ∣ n := by
        omega
      contradiction
    -- Using the fact that n ≡ 1 or 2 (mod 3)
    -- Using the fact that n ≡ 1 (mod 2)
    -- Solving the congruence in Lean
    omega
  rcases h2 with (h | h | h | h | h | h | h | h)
  · -- Case where n % 24 = 1
    simp [Nat.ModEq, Nat.pow_mod, h]
  · -- Case where n % 24 = 5
    simp [Nat.ModEq, Nat.pow_mod, h]
  · -- Case where n % 24 = 7
    simp [Nat.ModEq, Nat.pow_mod, h]
  · -- Case where n % 24 = 11
    simp [Nat.ModEq, Nat.pow_mod, h]
  · -- Case where n % 24 = 13
    simp [Nat.ModEq, Nat.pow_mod, h]
  · -- Case where n % 24 = 17
    simp [Nat.ModEq, Nat.pow_mod, h]
  · -- Case where n % 24 = 19
    simp [Nat.ModEq, Nat.pow_mod, h]
  · -- Case where n % 24 = 23
    simp [Nat.ModEq, Nat.pow_mod, h]