import Mathlib

/- Une cellule peut se diviser en 42 ou en 44 petites cellules.
Combien de divisions faut-il pour obtenir, à partir d'une cellule,
exactement 2017 cellules? -/

theorem combinatorics_607691: IsLeast {k: ℕ | ∃ a b, k = a + b ∧ 1 + 43 * a + 41 * b = 2017} 48 := by

  constructor

  -- the forward direction
  .
    simp
    use 24, 24

  -- the backward direction
  .
    intro k hk
    simp at hk
    obtain ⟨a, b, hk, h⟩ := hk
    rw [hk]
    clear hk
    omega