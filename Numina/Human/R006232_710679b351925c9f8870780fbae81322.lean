import Mathlib

/-856 Let k be an integer greater than 1. Express the integer
N = k ^ 3 - k ^ 2 + k - 1 in base −k. Show that
N = (k-1)(-k)^2+0(-k)^1+(k-1)(-k)^0-/

theorem number_theory_634975 (k N: ℤ) (h: N = k ^ 3 - k ^ 2 + k - 1) :
  N = (k - 1) * (-k) ^ 2 + 0 * (-k) ^ 1 + (k - 1) * (-k) ^ 0 := by

  simp [h]
  ring


