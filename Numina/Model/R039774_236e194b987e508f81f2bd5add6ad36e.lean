import Mathlib

open BigOperators Complex Filter Finset Real TopologicalSpace Topology

theorem calculus_17206 (s : Set (EuclideanSpace ℝ (Fin 2))) (p q : EuclideanSpace ℝ (Fin 2))
    (hp : p = ![5, 2]) (hq : q = ![-5 / 2, -1])
    (hs : s = {v : EuclideanSpace ℝ (Fin 2) | (inner v p / ‖p‖ ^ 2) • p = q})
    (m b : ℝ) (h : ∀ x ∈ s, x 1 = m * x 0 + b) :
    m = -5 / 2 ∧ b = -29 / 4 := by

  have heq : s = {v : EuclideanSpace ℝ (Fin 2) | 5 * (v 0) + 2 * (v 1) = -29 / 2} := by
    ext v
    simp only [hs, Set.mem_setOf_eq]
    rw [hp, hq]
    simp [inner, EuclideanSpace.norm_eq, Matrix.vecTail, Matrix.vecHead, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.sum_univ_succ, Fin.sum_univ_zero]
    constructor
    · -- Assume h_eq : ..., prove 5 * (v 0) + 2 * (v 1) = -29 / 2
      rintro h_eq
      have eq1 := congr_arg (fun x => x 0) h_eq
      have eq2 := congr_arg (fun x => x 1) h_eq
      norm_num [Matrix.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at eq1 eq2
      linarith
    · -- Assume 5 * (v 0) + 2 * (v 1) = -29 / 2, prove h_eq
      intro h_eq
      have eq1 : (5 * (v 0) + 2 * (v 1)) = -29 / 2 := by
        linarith
      have eq2 : (5 * (v 0) + 2 * (v 1)) / (29 : ℝ) = -1 / 2 := by
        nlinarith
      funext i
      fin_cases i <;> norm_num [Matrix.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at *
      <;> nlinarith

  have h2 := h (fun i => if i = 0 then (0 : ℝ) else (-29 / 4 : ℝ)) (by
    rw [heq]
    simp
    all_goals
      norm_num
  )
  simp [Matrix.vecHead, Matrix.vecTail] at h2
  have hb : b = -29 / 4 := by
    linarith

  have h3 := h (fun i => if i = 0 then (-29 / 10 : ℝ) else (0 : ℝ)) (by
    rw [heq]
    simp
    all_goals
      norm_num
  )
  simp [Matrix.vecHead, Matrix.vecTail] at h3
  have hm : m = -5 / 2 := by
    rw [hb] at h3
    nlinarith

  constructor
  · linarith [hm]
  · linarith [hb]