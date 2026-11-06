import Mathlib

theorem number_theory_43246 : 2020^2021 - ⌊(2020^2021 / 2021 : ℝ)⌋ * 2021 = 2020 := by
  norm_num
  <;> try { native_decide }