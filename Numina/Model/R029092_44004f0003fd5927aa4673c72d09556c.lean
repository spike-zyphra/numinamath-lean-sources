import Mathlib

theorem number_theory_179907 :
    ∀ N : ℕ, ∃ a ≥ N, ∀ n : ℕ, ¬ ∃ m : ℕ, m^2 = n^4 + a := by
  intro N
  use 8 * N + 2
  constructor
  · -- Show that $a \ge N$
    omega
  · -- Show that $\forall n : \mathbb{N}, \neg \exists m : \mathbb{N}, m^2 = n^4 + a$
    intro n
    intro h
    rcases h with ⟨m, hm⟩
    have h1 : m^2 = n^4 + 8 * N + 2 := by
      linarith
    -- Show $8 \nmid m^2 - a \implies \neg (m^2 = a + n^4)$
    have h2 : m^2 % 8 = 0 ∨ m^2 % 8 = 1 ∨ m^2 % 8 = 4 := by
      have h1 : m % 8 = 0 ∨ m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 3 ∨ m % 8 = 4 ∨ m % 8 = 5 ∨ m % 8 = 6 ∨ m % 8 = 7 := by
        omega
      rcases h1 with (h | h | h | h | h | h | h | h) <;> simp [pow_two, Nat.mul_mod, h]
    have h3 : (n^4 + 8 * N + 2) % 8 = 2 ∨ (n^4 + 8 * N + 2) % 8 = 3 := by
      by_cases h4 : n % 2 = 0
      · -- If n is even
        -- Then n^4 is divisible by 8.
        have h7 : n^4 % 8 = 0 := by
          have h4' : n % 2 = 0 := h4
          have h8 : n % 8 = 0 ∨ n % 8 = 2 ∨ n % 8 = 4 ∨ n % 8 = 6 := by 
            omega
          rcases h8 with (h8 | h8 | h8 | h8) <;> simp [h8, pow_succ, Nat.mul_mod]
        omega
      · -- Assume n is odd
        have h7 : n^4 % 8 = 1 := by
          have h4' : n % 2 = 1 := by 
            omega
          have h8 : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
            omega
          rcases h8 with (h8 | h8 | h8 | h8) <;> simp [h8, pow_succ, Nat.mul_mod]
        omega
    have h8 : m^2 % 8 = (n^4 + 8 * N + 2) % 8 := by
      omega
    omega