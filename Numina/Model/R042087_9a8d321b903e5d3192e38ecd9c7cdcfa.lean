import Mathlib

theorem number_theory_187974 :
    ∀ N : ℕ, ∃ z : ℕ, z > N ∧ ¬∃ a b c m n k : ℕ, a^(2 * m) + b^(2 * n) + c^(2 * k) = z := by
  intro N
  use 8 * N + 7
  constructor
  · -- Show that z > N
    omega
  · -- Let's show that it is not possible to sum three squares to get z
    intro h
    rcases h with ⟨a, b, c, m, n, k, h_eq⟩
    have h1 : a ^ (2 * m) % 8 = 0 ∨ a ^ (2 * m) % 8 = 1 ∨ a ^ (2 * m) % 8 = 4 := by
      have h2 : a ^ (2 * m) % 8 = 0 ∨ a ^ (2 * m) % 8 = 1 ∨ a ^ (2 * m) % 8 = 4 := by
        have h3 : ∀ (x : ℕ), x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
          intro x
          have h4 : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by
            omega
          rcases h4 with (h | h | h | h | h | h | h | h) <;> simp [Nat.pow_mod, h]
        have h4 : a ^ (2 * m) = (a ^ m) ^ 2 := by
          ring_nf
        have h5 : (a ^ m) ^ 2 % 8 = 0 ∨ (a ^ m) ^ 2 % 8 = 1 ∨ (a ^ m) ^ 2 % 8 = 4 := h3 (a ^ m)
        omega
      omega
    have h2 : b ^ (2 * n) % 8 = 0 ∨ b ^ (2 * n) % 8 = 1 ∨ b ^ (2 * n) % 8 = 4 := by
      have h2 : b ^ (2 * n) % 8 = 0 ∨ b ^ (2 * n) % 8 = 1 ∨ b ^ (2 * n) % 8 = 4 := by
        have h3 : ∀ (x : ℕ), x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
          intro x
          have h4 : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by
            omega
          rcases h4 with (h | h | h | h | h | h | h | h) <;> simp [Nat.pow_mod, h]
        have h4 : b ^ (2 * n) = (b ^ n) ^ 2 := by
          ring_nf
        have h5 : (b ^ n) ^ 2 % 8 = 0 ∨ (b ^ n) ^ 2 % 8 = 1 ∨ (b ^ n) ^ 2 % 8 = 4 := h3 (b ^ n)
        omega
      omega
    have h3 : c ^ (2 * k) % 8 = 0 ∨ c ^ (2 * k) % 8 = 1 ∨ c ^ (2 * k) % 8 = 4 := by
      have h2 : c ^ (2 * k) % 8 = 0 ∨ c ^ (2 * k) % 8 = 1 ∨ c ^ (2 * k) % 8 = 4 := by
        have h3 : ∀ (x : ℕ), x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
          intro x
          have h4 : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by
            omega
          rcases h4 with (h | h | h | h | h | h | h | h) <;> simp [Nat.pow_mod, h]
        have h4 : c ^ (2 * k) = (c ^ k) ^ 2 := by
          ring_nf
        have h5 : (c ^ k) ^ 2 % 8 = 0 ∨ (c ^ k) ^ 2 % 8 = 1 ∨ (c ^ k) ^ 2 % 8 = 4 := h3 (c ^ k)
        omega
      omega
    omega