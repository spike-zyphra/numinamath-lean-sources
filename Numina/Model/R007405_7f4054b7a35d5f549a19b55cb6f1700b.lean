import Mathlib

theorem number_theory_66595 (n : ℤ) (h₀ : Odd n) :
    ∃ a b, n = a^2 - b^2 := by
  obtain ⟨k, hk⟩ := h₀
  use k + 1, k
  rw [hk]
  ring