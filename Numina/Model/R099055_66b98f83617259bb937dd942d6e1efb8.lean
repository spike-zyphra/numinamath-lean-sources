import Mathlib

theorem number_theory_218434 (a b : ℤ) :
    (3 ∣ a + 1) → (3 ∣ 4 + 7 * a) ∧
    (11 ∣ 2 + a) ∧ (11 ∣ 35 - b) → (11 ∣ a + b) := by 
  intro h3 h
  rcases h with ⟨h3', h11a, h11b⟩
  omega