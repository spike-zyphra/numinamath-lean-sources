import Mathlib

theorem algebra_14263 {f : ℕ → ℝ} {d : ℝ} (hf: ∀n, f (n + 1) = f n + d) (hf₁: f 1 = 7/9) (hf₂: f 13 = 4/5) : f 7 = 71/90 := by
  have eq1 : f 13 = f 12 + d := hf 12
  have eq2 : f 12 = f 11 + d := hf 11
  have eq3 : f 11 = f 10 + d := hf 10
  have eq4 : f 10 = f 9 + d := hf 9
  have eq5 : f 9 = f 8 + d := hf 8
  have eq6 : f 8 = f 7 + d := hf 7
  have eq7 : f 7 = f 6 + d := hf 6
  have eq8 : f 6 = f 5 + d := hf 5
  have eq9 : f 5 = f 4 + d := hf 4
  have eq10 : f 4 = f 3 + d := hf 3
  have eq11 : f 3 = f 2 + d := hf 2
  have eq12 : f 2 = f 1 + d := hf 1
  norm_num [hf₁] at eq12
  linarith [hf₂, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]