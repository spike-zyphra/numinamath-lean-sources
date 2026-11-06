import Mathlib

theorem number_theory_101894 (n : ℤ) :
    (6 ∣ n - 4 ∧ 10 ∣ n - 8) ↔ ∃ k, n = 30 * k - 2 := by
  constructor
  · -- Assume (6 ∣ n - 4 ∧ 10 ∣ n - 8), prove ∃ k, n = 30 * k - 2
    intro h
    rcases h with ⟨h1, h2⟩
    have h1' : n % 6 = 4 := by 
      omega
    have h2' : n % 10 = 8 := by 
      omega
    have h3 : n % 30 = 28 := by
      omega
    refine ⟨(n + 2) / 30, by omega⟩
  · -- Assume ∃ k, n = 30 * k - 2, prove (6 ∣ n - 4 ∧ 10 ∣ n - 8)
    rintro ⟨k, hk⟩
    constructor
    · -- Prove 6 divides n - 4
      have h1 : n - 4 = 6 * (5 * k - 1) := by 
        rw [hk]
        omega
      exact ⟨5 * k - 1, h1⟩
    · -- Prove 10 divides n - 8
      have h2 : n - 8 = 10 * (3 * k - 1) := by 
        rw [hk]
        omega
      exact ⟨3 * k - 1, h2⟩