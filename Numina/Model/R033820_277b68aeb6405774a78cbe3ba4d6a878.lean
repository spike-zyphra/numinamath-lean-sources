import Mathlib

theorem algebra_12931 {x : ℂ} (hx : x^2 + x = -1) : x^2019 = 1 := by
  have h1 : x^2 = -x - 1 := by
    calc
      x^2 = (x ^2 + x) - x := by ring_nf
      _ = -1 - x := by rw [hx]
      _ = -x - 1 := by ring_nf

  have h2 : x^3 = 1 := by
    calc
      x^3 = x * x^2 := by ring_nf
      _ = x * (-x - 1) := by rw [h1]
      _ = -x^2 - x := by ring_nf
      _ = -(-x -1) - x := by rw [h1]
      _ = 1 := by ring_nf

  calc
    x^2019 = (x ^3)^673 := by ring_nf
    _ = (1)^673 := by rw [h2]
    _ = 1 := by norm_num