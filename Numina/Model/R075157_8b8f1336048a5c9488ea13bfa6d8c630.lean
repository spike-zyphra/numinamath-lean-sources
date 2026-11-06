import Mathlib

theorem number_theory_290482 (p : ℕ) (hp : p > 0) :
    (p * 19) % 7 = 4 ∧ (p * 19) % 11 = 1 → p ≥ 40 := by
  intro h
  rcases h with ⟨h1, h2⟩
  omega