import Mathlib

theorem number_theory_255540 (n : ℕ) :
    5 ∣ 3 * (n ^ 2 + n) + 7 ↔ ∃ t, n = 5 * t + 2 := by
  constructor
  · -- Assume 5 divides 3 * (n ^ 2 + n) + 7, prove ∃ t, n = 5 * t + 2
    intro h
    have h1 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1)
    · -- Case n % 5 = 0
      have h2 : (3 * (n ^ 2 + n) + 7) % 5 ≠ 0 := by
        have h3 : n % 5 = 0 := h1
        have h4 : n ^ 2 % 5 = 0 := by
          simp [Nat.pow_mod, h3]
        have h5 : n % 5 = 0 := h3
        omega
      omega
    · -- Case n % 5 = 1
      have h2 : (3 * (n ^ 2 + n) + 7) % 5 ≠ 0 := by
        have h3 : n % 5 = 1 := h1
        have h4 : n ^ 2 % 5 = 1 := by
          simp [Nat.pow_mod, h3]
        have h5 : n % 5 = 1 := h3
        omega
      omega
    · -- Case n % 5 = 2
      have h2 : n % 5 = 2 := h1
      use (n - 2) / 5
      omega
    · -- Case n % 5 = 3
      have h2 : (3 * (n ^ 2 + n) + 7) % 5 ≠ 0 := by
        have h3 : n % 5 = 3 := h1
        have h4 : n ^ 2 % 5 = 4 := by
          simp [Nat.pow_mod, h3]
        have h5 : n % 5 = 3 := h3
        omega
      omega
    · -- Case n % 5 = 4
      have h2 : (3 * (n ^ 2 + n) + 7) % 5 ≠ 0 := by
        have h3 : n % 5 = 4 := h1
        have h4 : n ^ 2 % 5 = 1 := by
          simp [Nat.pow_mod, h3]
        have h5 : n % 5 = 4 := h3
        omega
      omega
  · -- Assume ∃ t, n = 5 * t + 2, prove 5 ∣ 3 * (n ^ 2 + n) + 7
    rintro ⟨t, ht⟩
    rw [ht]
    have eq1 : 3 * ((5 * t + 2) ^ 2 + (5 * t + 2)) + 7 = 75 * t^2 + 75 * t + 25 := by ring
    rw [eq1]
    omega