import Mathlib

open Real

/-If the human race after the flood multiplied from 6 people and if we assume that two hundred years later
the number of people increased to a million, the question is: by what fraction should the population have increased annually?-/

theorem algebra_221942 (x: ℝ) (h1: 0 < x) (h2: (1 + x) ^ (200: ℝ) * 6 = 1000000):
  x = (500000 / 3) ^ ((1: ℝ) / 200) - 1 := by

  suffices 1 + x = (500000 / 3) ^ ((1: ℝ) / 200) by
    linarith
  set y:= 1 + x
  replace h2: y ^ (200: ℝ) = 500000 / 3 := by
    rw [show y ^ (200: ℝ) = y ^ (200: ℝ) * 6 / 6 by field_simp]
    rw [h2]
    norm_num
  have f: y = (y ^ (200: ℝ)) ^ ((1: ℝ) / 200) := by
    rw [← Real.rpow_mul]
    simp
    simp [y]
    linarith
  rw [f, h2]
