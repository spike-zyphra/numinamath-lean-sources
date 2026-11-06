import Mathlib


theorem algebra_6113 {f : ℤ → ℤ} (hf1 : ∀ x, f (x + 4) - f x = 8 * x + 20) (hf2 : ∀ x, f (x ^ 2 - 1) = (f x - x) ^ 2 + x ^ 2 - 2) :
    f 0 = -1 ∧ f 1 = 1 := by

  have eq1 := hf1 0
  norm_num at eq1

  have eq2 := hf1 1
  norm_num at eq2

  have eq3 := hf1 2
  norm_num at eq3

  have eq4 := hf1 3
  norm_num at eq4

  have eq5 := hf1 4
  norm_num at eq5

  have eq6 := hf1 (-1)
  norm_num at eq6

  have eq7 := hf1 (-2)
  norm_num at eq7

  have eq8 := hf1 (-3)
  norm_num at eq8

  have eq9 := hf1 (-4)
  norm_num at eq9

  have eq10 := hf2 0
  norm_num at eq10

  have eq11 := hf2 1
  norm_num at eq11

  have eq12 := hf2 2
  norm_num at eq12

  have eq13 := hf2 3
  norm_num at eq13

  have eq14 := hf2 (-1)
  norm_num at eq14

  have eq15 := hf2 (-2)
  norm_num at eq15

  have eq16 := hf2 (-3)
  norm_num at eq16

  have h1 : f 0 = -1 := by
    nlinarith [sq_nonneg (f 0 + 1), sq_nonneg (f 1 - 1), sq_nonneg (f 2 - 2), sq_nonneg (f 3 - 11), sq_nonneg (f 4 - 19), sq_nonneg (f 8 - 73)]
  have h2 : f 1 = 1 := by
    rw [h1] at eq11
    nlinarith

  exact ⟨h1, h2⟩