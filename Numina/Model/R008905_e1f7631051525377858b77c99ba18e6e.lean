import Mathlib

theorem number_theory_4651 {n : ℤ} : (Even n → n^2 % 4 = 0) ∧ (Odd n → n^2 % 4 = 1) := by
  constructor
  · -- Assume n is even, we need to prove n^2 % 4 = 0
    intro h
    obtain ⟨k, hk⟩ := h
    have : n^2 = 4 * k^2 := by 
      rw [hk]
      ring
    rw [this]
    omega
  · -- Assume n is odd, we need to prove n^2 % 4 = 1
    intro h
    obtain ⟨k, hk⟩ := h
    have : n^2 = 4 * k^2 + 4 * k + 1 := by 
      rw [hk]
      ring
    rw [this]
    omega