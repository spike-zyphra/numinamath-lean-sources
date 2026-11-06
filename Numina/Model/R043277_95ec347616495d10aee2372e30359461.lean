import Mathlib

theorem number_theory_269543 (n : ℕ) (h : Odd n) : 24 ∣ n^3 + 23 * n := by
  have h1 : n % 2 = 1 := by
    rcases h with ⟨k, hk⟩
    omega
  have h2 : (n ^ 3 + 23 * n) % 8 = 0 := by
    have h3 : n % 2 = 1 := h1
    have h4 : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
      omega
    rcases h4 with (h4 | h4 | h4 | h4) <;> simp [h4, Nat.add_mod, Nat.mul_mod, pow_succ, Nat.pow_mod]
  -- Now prove divisibility by 3
  have h3 : (n ^ 3 + 23 * n) % 3 = 0 := by
    have h4 : n % 2 = 1 := h1
    have h5 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
      omega
    rcases h5 with (h5 | h5 | h5) <;> simp [h5, Nat.add_mod, Nat.mul_mod, pow_succ, Nat.pow_mod]
  omega