import Mathlib

/-Brenda is going from $(-4,5)$ to $(5,-4)$, but she needs to stop by the origin on the way. How far does she have to travel?-/
theorem algebra_10357 (A B C : EuclideanSpace ℝ (Fin 2))
(hA : A = (λ i => if i = 0 then -4 else 5)) (hB : B = (λ i => if i = 0 then 0 else 0))
(hC : C = (λ i => if i = 0 then 5 else -4)) :
dist A B + dist B C = 2 * Real.sqrt 41 := by
-- This is a straightforward simplification using EuclideanSpace.dist_eq and the assumptions
  simp [EuclideanSpace.dist_eq, hA, hB, hC]; norm_num; rw [two_mul]