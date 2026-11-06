import Mathlib

theorem algebra_10357 (A B C : EuclideanSpace ℝ (Fin 2))
(hA : A = (λ i => if i = 0 then -4 else 5)) (hB : B = (λ i => if i = 0 then 0 else 0))
(hC : C = (λ i => if i = 0 then 5 else -4)) :
dist A B + dist B C = 2 * Real.sqrt 41 := by
  -- Substitute and simplify the points coordinates into cartesian vectors.
  have h1 : dist A B = Real.sqrt ((-4 : ℝ) ^ 2 + (5 : ℝ) ^ 2) := by
    rw [dist_eq_norm]
    rw [hA, hB]
    simp [norm_eq_sqrt_real_inner, Fin.sum_univ_two, Fin.sum_univ_zero, Fin.sum_univ_one]
    all_goals ring_nf
  -- Compute substitution h1.
  have h2 : dist A B = Real.sqrt 41 := by
    rw [h1]
    ring_nf
  -- Compute dist B C.
  have h3 : dist B C = Real.sqrt 41 := by
    rw [dist_eq_norm]
    rw [hB, hC]
    simp [norm_eq_sqrt_real_inner, Fin.sum_univ_two, Fin.sum_univ_zero, Fin.sum_univ_one]
    ring_nf
  -- Final step: combine.
  rw [h2, h3]
  ring