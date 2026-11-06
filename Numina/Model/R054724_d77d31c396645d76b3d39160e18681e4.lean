import Mathlib

theorem algebra_81885 (a j : ℕ) (ha : a = 3 * (j - (2 * (a - j))) ∧ a = j + 29) :
    a + j = 79 := by
  rcases ha with ⟨h1, h2⟩
  omega