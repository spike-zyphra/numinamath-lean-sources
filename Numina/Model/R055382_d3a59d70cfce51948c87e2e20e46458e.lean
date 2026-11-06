import Mathlib

theorem number_theory_101886 (n : ℤ) :
    (5 ∣ 3 * n - 2) ∧ (7 ∣ 2 * n + 1) ↔ ∃ k, n = 35 * k - 11 := by
  constructor
  · -- Assume (5 | 3n - 2) ∧ (7 | 2n + 1), prove ∃ k, n = 35k - 11
    rintro ⟨h₁, h₂⟩
    have h3 : n % 5 = 4 := by
      omega
    have h4 : n % 7 = 3 := by
      omega
    refine ⟨(n + 11) / 35, ?_⟩
    omega
  · -- Assume ∃ k, n = 35k - 11, prove (5 | 3n - 2) ∧ (7 | 2n + 1)
    rintro ⟨k, rfl⟩
    constructor
    · -- Show 5 divides 3n - 2
      omega
    · -- Show 7 divides 2n + 1
      omega