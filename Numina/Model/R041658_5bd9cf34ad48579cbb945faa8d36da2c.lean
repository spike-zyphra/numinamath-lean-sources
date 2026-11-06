import Mathlib
open Mathlib

lemma algebra_1176 (lemonJuice : ℚ) (sugar : ℚ) (water : ℚ) (h1 : lemonJuice = 100) (h2 : sugar = 100) (h3 : water = 400) (lemonJuiceCalories sugarCalories waterCalories : ℚ) (h4 : lemonJuiceCalories = 25 * lemonJuice / 100) (h5 : sugarCalories = 386 * sugar / 100) (h6 : waterCalories = 0) : (lemonJuiceCalories + sugarCalories + waterCalories) / (lemonJuice + sugar + water) * 200 = 137 := by
  rw [h1] at *
  rw [h2] at *
  rw [h3] at *
  rw [h4] at *
  rw [h5] at *
  rw [h6] at *
  norm_num