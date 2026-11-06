import Mathlib

theorem algebra_189030 {x y : ℕ} (hxy : x * y = 4500) (hxy' : (10 * x + 3) * y = 4380) :
    x = 6075 ∧ y = 750 := by

  have eq1 : 10 * (x * y) + 3 * y = 4380 := by
    linarith [hxy']

  have eq2 : x * y = 4500 := hxy
  omega