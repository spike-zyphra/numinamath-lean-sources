import Mathlib

theorem number_theory_284507
    (a b : ℤ)
    (ha : Even a)
    (hb : Odd b) :
    Odd (a - b) := by
  rcases ha with ⟨k, h1⟩
  rcases hb with ⟨m, h2⟩
  use k - m - 1
  linarith [h1, h2]