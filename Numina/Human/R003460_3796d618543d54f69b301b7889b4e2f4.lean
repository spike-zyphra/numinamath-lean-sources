import Mathlib

/- 4. Find the smallest natural $n>1$, for which the sum of no two natural powers is a perfect square of a natural number.

#-/
theorem number_theory_184788 :
    IsLeast {n : ℕ | 1 < n ∧ ∀ m k : ℕ, ¬∃ j : ℕ, j ^ 2 = n ^ m + n ^ k} 4 := by
  constructor
  · -- First, we verify that 4 belongs to the set, which means that 4 ^ m + 4 ^ k is never a square for any n, m ≥ 0.
    norm_num
    -- Assume on the contrary that 4 ^ m + 4 ^ k = z ^ 2 for some m, k, z ∈ ℕ.
    intro m k z h₀
    -- Analyze the equation modulo 3, note that 4 ^ m + 4 ^ k ≡ 1 + 1 [MOD 3].
    have h₁ : (4 ^ m + 4 ^ k) % 3 = 2 := by
      simp [Nat.add_mod, Nat.pow_mod]
    -- However, z ^ 2 % 3 = 0 or 1.
    have h₂ : z ^ 2 % 3 = 0 ∨ z ^ 2 % 3 = 1 := by
      have : z % 3 = 0 ∨ z % 3 = 1 ∨ z % 3 = 2 := by omega
      rcases this with (h | h | h)
      <;> norm_num [Nat.pow_mod, h]
    -- We get a contradiction.
    omega
  · -- Now we show 4 is the least element, which means that 2, 3 does not satisfy the condition.
    intro n hn
    obtain ⟨hn, hn'⟩ := hn
    by_contra!
    interval_cases n
    . -- Case n = 2 : 2 ^ 1 + 2 ^ 1 = 2 ^ 2.
      absurd hn' 1 1
      use 2
      rfl
    . -- Case n = 3 : 3 ^ 3 + 3 ^ 2 = 6 ^ 2.
      absurd hn' 3 2
      use 6
      rfl