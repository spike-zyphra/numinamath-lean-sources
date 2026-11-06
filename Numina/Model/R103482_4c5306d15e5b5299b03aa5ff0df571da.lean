import Mathlib

theorem number_theory_252331 :
    ¬∃ x y : ℕ, x*3+y*7=11 ∧
    ∀ n ≥ 12, ∃ x y : ℕ, x*3+y*7=n := by
  intro h
  rcases h with ⟨x, y, h1, h2⟩
  have h3 : x ≤ 3 := by omega
  have h4 : y ≤ 1 := by omega
  omega