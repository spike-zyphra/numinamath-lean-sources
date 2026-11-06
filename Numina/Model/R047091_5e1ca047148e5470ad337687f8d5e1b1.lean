import Mathlib


theorem number_theory_284637 (S : Finset ℝ) (hS : S = {(8 / 9), (7 / 8), (66 / 77), (55 / 66), (4 / 5)}) : S.max' (by simp [hS]) = ((8 : ℝ) / (9 : ℝ)) := by
  simp only [hS]
  norm_num [Finset.max']