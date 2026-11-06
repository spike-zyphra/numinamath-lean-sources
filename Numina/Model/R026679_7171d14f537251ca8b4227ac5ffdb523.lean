import Mathlib

theorem number_theory_256072 (a : ℤ) :
    IsCoprime a (a + 1) ∧ IsCoprime (a + 1) (2 * a + 1) ∧ IsCoprime (2 * a + 1) a := by
  constructor
  · -- Show that IsCoprime a (a + 1)
    rw [IsCoprime]
    use -1, 1
    ring
  constructor
  · -- Show that IsCoprime (a + 1) (2 * a + 1)
    rw [IsCoprime]
    use 2, -1
    ring
  · -- Show that IsCoprime (2 * a + 1) a 
    rw [IsCoprime]
    use 1, -2
    ring