import Mathlib

theorem number_theory_279550 (a b : ℕ) (ha : a > 0) (hb : b > 0)
    (h1 : (a + b) ∈ Finset.Icc 10 99) (h2 : (a - b) ∈ Finset.Icc 10 99)
    (h3 : (a + b) * (a - b) = 645) :
    a = 29 ∧ b = 14 := by
  rw [Finset.mem_Icc] at h1 h2
  rcases h1 with ⟨h1l, h1u⟩
  rcases h2 with ⟨h2l, h2u⟩
  interval_cases h : a + b <;> omega