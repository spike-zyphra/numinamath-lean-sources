import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

theorem algebra_2400
  (a : ℝ)
  (h : a ≠ 0) :
  ¬ (0 = -1 / a) := by
  intro h1
  have h2 : -1 / a = 0 := by
    linarith
  field_simp [h] at h2 ⊢
  all_goals
  linarith