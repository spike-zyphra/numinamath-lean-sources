import Mathlib

theorem number_theory_93417 (a : Fin 8 → Fin 8 → ℕ)
    (ha : ∀ i j, a i j = i * 8 + j + 1) :
    a 0 0 + a 0 7 + a 7 0 + a 7 7 = 130 := by

  have h1 : a 0 0 = 0 * 8 + 0 + 1 := ha 0 0
  have h2 : a 0 7 = 0 * 8 + 7 + 1 := ha 0 7
  have h3 : a 7 0 = 7 * 8 + 0 + 1 := ha 7 0
  have h4 : a 7 7 = 7 * 8 + 7 + 1 := ha 7 7

  simp [h1, h2, h3, h4]
  all_goals omega