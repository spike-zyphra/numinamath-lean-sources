import Mathlib

theorem algebra_139005 (x : ℝ) (hx : x = 1 / 2) :
    (1 + y) * x = 1 ↔ y = 1 := by
  rw [hx]
  constructor
  · -- Assume (1 + y) * (1/2) = 1, prove y = 1
    intro h
    have eq1 : (1 + y) * (1 / 2 : ℝ) = 1 := h
    have eq2 : 1 + y = 2 := by
      linarith
    linarith
  · -- Assume y = 1, prove (1 + y) * (1/2) = 1
    intro h
    rw [h]
    norm_num