import Mathlib

theorem algebra_255475 (d : ℝ) (h : d > 0) (h1 : (3 / 2) * d = 2 * (d - 3)) (h2 : (2 / 3) * d = 1.5 * (d - 3)) :
    d = 12 := by
  ring_nf at h1 h2 ⊢ 
  linarith -- Lean automatically find contradiction or solve linear equalities.