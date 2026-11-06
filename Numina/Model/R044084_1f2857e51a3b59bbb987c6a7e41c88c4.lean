import Mathlib

theorem number_theory_291962 (n : ℕ) :
    10 ∣ n^2 + (n + 1)^2 + (n + 2)^2 + (n + 3)^2 ↔ ∃ k, n = 5 * k + 1 := by
  constructor
  · -- Assume 10 divides the sum, prove there exists a k such that n = 5 * k + 1
    intro h
    have h1 : n ^ 2 + (n + 1) ^ 2 + (n + 2) ^ 2 + (n + 3) ^ 2 = 4 * n^2 + 12 * n + 14 := by
      ring
    rw [h1] at h
    have h2 : n % 5 = 1 := by
      have h3 : (4 * n ^ 2 + 12 * n + 14) % 5 = 0 := by
        omega
      have : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
        omega
      rcases this with (h | h | h | h | h) <;> simp [h, Nat.add_mod, Nat.mul_mod, Nat.pow_mod] at h3 <;> omega
    refine ⟨n / 5, by omega⟩
  · -- Assume there exists a k such that n = 5 * k + 1, prove the sum is divisible by 10
    rintro ⟨k, hk⟩
    have h1 : n ^ 2 + (n + 1) ^ 2 + (n + 2) ^ 2 + (n + 3) ^ 2 = 4 * n^2 + 12 * n + 14 := by
      ring
    rw [h1]
    rw [show n = 5 * k + 1 by omega]
    ring_nf
    <;> omega