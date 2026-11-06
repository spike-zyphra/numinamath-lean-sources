import Mathlib

theorem number_theory_1698 : (36 / 19 : ℝ) > 9 / 5 ∧ (36 / 19 : ℝ) > 12 / 7 ∧ (36 / 19 : ℝ) > 27 / 17 ∧ (36 / 19 : ℝ) > 54 / 29 ∧ (27 / 17 : ℝ) < 9 / 5 ∧ (27 / 17 : ℝ) < 12 / 7 ∧ (27 / 17 : ℝ) < 36 / 19 ∧ (27 / 17 : ℝ) < 54 / 29 := by
  constructor
  · -- Show that (36 / 19 : ℝ) > 9 / 5
    norm_num
  constructor
  · -- Show that (36 / 19 : ℝ) > 12 / 7
    norm_num
  constructor
  · -- Show that (36 / 19 : ℝ) > 27 / 17
    norm_num
  constructor
  · -- Show that (36 / 19 : ℝ) > 54 / 29
    norm_num
  constructor
  · -- Show that (27 / 17 : ℝ) < 9 / 5
    norm_num
  constructor
  · -- Show that (27 / 17 : ℝ) < 12 / 7
    norm_num
  constructor
  · -- Show that (27 / 17 : ℝ) < 36 / 19
    norm_num
  · -- Show that (27 / 17 : ℝ) < 54 / 29
    norm_num