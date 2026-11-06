import Mathlib

theorem number_theory_219141 (n : ℤ) (h₀ : Odd n) :
    ∃ a b, a^2 - b^2 = n := by
  obtain ⟨k, hk⟩ := h₀
  use k + 1, k
  nlinarith [hk]