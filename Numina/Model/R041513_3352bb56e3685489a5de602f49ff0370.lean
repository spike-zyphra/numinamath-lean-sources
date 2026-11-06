import Mathlib

theorem algebra_128229 {x : ℝ} (hx : x = 0.8) :
    (1 + y) * x = 1 ↔ y = 0.25 := by
  rw [hx]
  constructor
  · -- Assume (1 + y) * 0.8 = 1, prove y = 0.25
    intro h
    have h1 : (1 + (y : ℝ)) * (0.8 : ℝ) = 1 := by
      simpa using h
    have h2 : y = (0.25 : ℝ) := by
      norm_num at h1 ⊢
      linarith
    exact_mod_cast h2
  · -- Assume y = 0.25, prove (1 + y) * 0.8 = 1
    intro h
    rw [h]
    norm_num