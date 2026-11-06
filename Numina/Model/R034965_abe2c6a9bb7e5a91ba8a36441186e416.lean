import Mathlib

theorem algebra_288270 {x y z u : ℝ}
    (h1 : x + y / 4 = 6 * z)
    (h2 : y + x / 5 = 8 * z)
    (h3 : x + 46 + (y - 46) / 3 = 30 * u )
    (h4 : y - 46 + (x + 46) / 3 = 36 * u ) :
    x = 440 ∧ y = 748 ∧ z = 209/2 ∧ u = 24 := by
  have eq1 : x = 440 := by
    linarith
  -- Proving y
  have eq2 : y = 748 := by
    linarith
  -- Proving z
  have eq3 : z = 209 / 2 := by
    linarith
  -- Proving u
  have eq4 : u = 24 := by
    linarith
  exact ⟨eq1, eq2, eq3, eq4⟩