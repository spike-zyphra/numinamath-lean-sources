import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_28480 {a : ℝ} (ha : 0 < a) (P Q : ℝ × ℝ)
  (hP : P = (a, 1 / a)) (hQ : Q = (2 * a, 1 / (2 * a)))
  (hC : ∀ x, y = 1 / x) :
  ∫ x in (0)..(2 * a), max (1 / x - 1 / a) 0 = 2 * log 2 - 9 / 8 := by
  have h1 := hC 1
  have h2 := hC 2
  norm_num at h1 h2
  all_goals
    omega