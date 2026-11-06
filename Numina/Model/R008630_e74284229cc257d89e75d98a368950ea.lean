import Mathlib

theorem algebra_21321 :(Finset.card {(x, y) : Finset.Icc 1 6 × Finset.Icc 1 6 | x.1 + y.1 = 7}) / (36 : ℝ) = 1 / 6 := by
  have h1 : Finset.card {(x, y) : Finset.Icc 1 6 × Finset.Icc 1 6 | x.1 + y.1 = 7} = 6 := by
    native_decide
  rw [h1]
  norm_num