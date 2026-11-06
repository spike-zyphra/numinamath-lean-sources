import Mathlib

theorem algebra_200504 {n t : ℕ} (ht : t > 0) (h : n * 5 + t * 4 = 100 ∧ t * 5 + n * 4 = 64) :
    t = 3 := by
  obtain ⟨h1, h2⟩ := h
  omega