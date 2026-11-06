import Mathlib

theorem algebra_250966 (n : ℕ) :
    ∃ x y, n = (x + 1 / (x : ℚ)) / (y + 1 / (y : ℚ)) ↔ n = 1 := by
  use 1, 1
  constructor
  · -- Assume n = (1 + 1/1) / (1 + 1/1), prove n = 1
    intro h
    norm_num at h ⊢
    exact_mod_cast h
  · -- Assume n = 1, prove n = (1 + 1/1) / (1 + 1/1)
    intro h
    rw [h]
    norm_num