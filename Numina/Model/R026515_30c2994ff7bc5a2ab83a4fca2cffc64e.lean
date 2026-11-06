import Mathlib

theorem number_theory_182690 (x y : ℤ) (hx : x = 25530) (hy : y = 29464) :
    ∃ n : ℕ, n > 0 ∧ n^2 = x^2 + y^2 := by
  use 38986
  constructor
  · norm_num -- check that 38986 > 0
  · rw [hx, hy]
    norm_num -- automatically compute the arithmetic