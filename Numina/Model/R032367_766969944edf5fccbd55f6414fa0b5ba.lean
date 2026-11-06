import Mathlib

theorem number_theory_160471 (n : ℕ) :
    ∃ a b, a^2 - b^2 = n^3 ∧
    ∑ i ∈ Finset.range n, (i + 1)^3 = n^2 * (n + 1)^2 / 4 := by 
  have h2 : ∑ i in Finset.range n, (i + 1) ^ 3 = n ^ 2 * (n + 1) ^ 2 / 4 := by
    have h2 : ∀ n : ℕ, ∑ i in Finset.range n, (i + 1) ^ 3 = n ^ 2 * (n + 1) ^ 2 / 4 := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        simp [add_assoc]
        ring_nf
        omega
    specialize h2 n
    simpa using h2 
  use n * (n + 1) / 2, n * (n - 1) / 2
  constructor
  · 
    have h3 : (n * (n + 1)) % 2 = 0 := by
      have h1 : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases h1 with (h1 | h1)
      · 
        simp [Nat.mul_mod, Nat.add_mod, h1]
      · 
        simp [Nat.mul_mod, Nat.add_mod, h1]
    have h4 : (n * (n - 1)) % 2 = 0 := by
      have h3 : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases h3 with (h3 | h3)
      · 
        simp [Nat.mul_mod, Nat.sub_mod_eq_zero_of_mod_eq, h3, Nat.add_mod]
      · 
        simp [Nat.mul_mod, Nat.sub_mod_eq_zero_of_mod_eq, h3, Nat.add_mod]
    have h9 : ((n * (n + 1) / 2 : ℕ) ) ^ 2 - ((n * (n - 1) / 2 : ℕ) ) ^ 2 = n ^ 3 := by
      have h10 : (n * (n + 1) : ℕ) % 2 = 0 := h3
      have h11 : (n * (n - 1) : ℕ) % 2 = 0 := h4
      have h12 : 4 * ((n * (n + 1) / 2 : ℕ) ^ 2 - (n * (n - 1) / 2 : ℕ) ^ 2) = 4 * (n ^ 3 : ℕ) := by
        have h13 : 4 * ((n * (n + 1) / 2 : ℕ) ^ 2) = (n * (n + 1)) ^ 2 := by
          have h14 : (n * (n + 1) : ℕ) % 2 = 0 := h3
          have h16 : ∃k, n * (n + 1) = 2 * k := by 
            refine' ⟨n * (n + 1) / 2, by omega⟩
          rcases h16 with ⟨k, hk⟩
          have h17 : (n * (n + 1) / 2 : ℕ) = k := by
            omega
          rw [h17]
          have h18 : 4 * (k ^ 2) = (2 * k) ^ 2 := by ring
          rw [h18]
          rw [show (2 * k) = n * (n + 1) by linarith [hk]]
        have h14 : 4 * ((n * (n - 1) / 2 : ℕ) ^ 2) = (n * (n - 1)) ^ 2 := by
          have h15 : (n * (n - 1) : ℕ) % 2 = 0 := h4
          have h17 : ∃ k, n * (n - 1) = 2 * k := by
            refine' ⟨n * (n - 1) / 2, by omega⟩
          rcases h17 with ⟨k, hk⟩
          have h18 : (n * (n - 1) / 2 : ℕ) = k := by
            omega
          rw [h18]
          have h19 : 4 * (k ^ 2) = (2 * k) ^ 2 := by ring
          rw [h19]
          rw [show (2 * k) = n * (n - 1) by linarith [hk]]
        have h18 : 4 * ((n * (n + 1) / 2 : ℕ) ^ 2 - (n * (n - 1) / 2 : ℕ) ^ 2) = (n * (n + 1)) ^ 2 - (n * (n - 1)) ^ 2 := by
          omega
        have h19 : (n * (n + 1)) ^ 2 - (n * (n - 1)) ^ 2 = 4 * (n ^ 3 : ℕ) := by
          cases n with
          | zero =>
            simp
          | succ n =>
            simp [Nat.pow_succ, Nat.pow_zero, Nat.mul_add, Nat.add_mul, Nat.add_assoc]
            ring_nf
            omega
        omega
      omega
    exact h9 
  · 
    exact h2