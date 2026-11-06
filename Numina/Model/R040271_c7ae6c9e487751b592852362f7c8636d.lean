import Mathlib

theorem algebra_14117 : IsLeast {y : ℝ | ∃ x, y = 5 * x ^ 2 - 20 * x + 1357} 1337 := by
  constructor
  · -- Show that 1337 is in the set
    use 2
    norm_num
  · -- Show that 1337 is indeed the least
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h1 : 5 * x ^ 2 - 20 * x + 1357 ≥ 1337 := by
      have h2 : 5 * (x - 2) ^ 2 ≥ 0 := by
        have h3 : (x - 2) ^ 2 ≥ 0 := sq_nonneg (x - 2)
        nlinarith
      linarith
    linarith [hx, h1]