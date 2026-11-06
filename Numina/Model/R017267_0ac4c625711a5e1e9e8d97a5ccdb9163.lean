import Mathlib

theorem number_theory_198308 (n : ℕ) :
    10 ∣ ∑ i ∈ Finset.range 4, (n + i) ^ 2 ↔ ∃ t, n = 5 * t + 1 := by
  have h1 : ∑ i in Finset.range 4, (n + i) ^ 2 = 4 * n^2 + 12 * n + 14 := by
    simp [Finset.sum_range_succ]
    ring
  rw [h1]
  constructor
  · -- Assume 10 divides the sum, prove there exists t such that n = 5 * t + 1
    intro h
    have h2 : (4 * n ^ 2 + 12 * n + 14) % 10 = 0 := by
      omega
    have h3 : n % 5 = 1 := by
      have h5 : (4 * n ^ 2 + 12 * n + 14) % 5 = 0 := by
        omega
      have h6 : n % 5 = 1 := by
        have h7 : (4 * n ^ 2 + 12 * n + 14) % 5 = 0 := h5
        have h8 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
          omega
        rcases h8 with (h | h | h | h | h) <;> simp [h, Nat.pow_mod, Nat.mul_mod, Nat.add_mod] at h7 <;> tauto
      exact h6
    refine ⟨n / 5, by omega⟩
  · -- Assume there exists t such that n = 5 * t + 1, prove 10 divides the sum
    rintro ⟨t, ht⟩
    rw [ht]
    have h2 : (4 * (5 * t + 1) ^ 2 + 12 * (5 * t + 1) + 14) % 10 = 0 := by
      ring_nf
      omega
    omega