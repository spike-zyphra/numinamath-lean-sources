import Mathlib

theorem number_theory_256693 (n : ℕ) (h₀ : Odd n) : n^2 ≡ 1 [MOD 8] := by
  have h1 : n % 2 = 1 := by
    exact Nat.odd_iff.1 h₀
  have h4 : ∀ k, n = 2 * k + 1 → n ^ 2 % 8 = 1 := by
    intro k hk
    rw [hk]
    have h6 : (2 * k + 1) ^ 2 % 8 = 1 := by
      have h1 : (2 * k + 1) ^ 2 = 4 * k^2 + 4 * k + 1 := by
        ring
      rw [h1]
      have h2 : (4 * k ^ 2 + 4 * k + 1) % 8 = 1 := by
        have h3 : (k : ℕ) % 2 = 0 ∨ (k : ℕ) % 2 = 1 := by omega
        rcases h3 with (h | h)
        · -- k is even
          have h4 : k % 2 = 0 := h
          have : (k : ℕ) = 2 * ((k : ℕ) / 2) := by
            omega
          rw [this]
          ring_nf
          <;> omega
        · -- k is odd
          have h4 : k % 2 = 1 := h
          have : (k : ℕ) = 2 * ((k : ℕ) / 2) + 1 := by
            omega
          rw [this]
          ring_nf
          <;> omega
      omega
    omega
  obtain ⟨k, hk⟩ := h₀
  specialize h4 k hk
  exact h4