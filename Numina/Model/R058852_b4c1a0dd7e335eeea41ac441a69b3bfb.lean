import Mathlib

theorem number_theory_234726 (a b : ℕ) : a^2 - 3 * b^2 ≠ 8 := by 
  by_contra h
  have h1 : a^2 - 3 * b^2 = 8 := by 
    omega
  have h2 : a^2 % 3 = 0 ∨ a^2 % 3 = 1 := by 
    have h3 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by 
      omega
    rcases h3 with (h3 | h3 | h3)
    · -- If a ≡ 0 (mod 3), then a² ≡ 0 (mod 3)
      norm_num [Nat.pow_mod, h3]
    · -- If a ≡ 1 (mod 3), then a² ≡ 1 (mod 3)
      norm_num [Nat.pow_mod, h3]
    · -- If a ≡ 2 (mod 3), then a² ≡ 4 ≡ 1 (mod 3)
      norm_num [Nat.pow_mod, h3]
  have h3 : (a^2 - 3 * b^2) % 3 = 8 % 3 := by 
    omega
  norm_num at h3 
  rcases h2 with (h2 | h2)
  · -- Case where a² ≡ 0 (mod 3)
    omega
  · -- Case where a² ≡ 1 (mod 3)
    omega