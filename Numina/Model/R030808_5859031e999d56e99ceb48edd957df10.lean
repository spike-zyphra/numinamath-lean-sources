import Mathlib

open BigOperators Real


theorem inequalities_226457
  (A B C D : EuclideanSpace ℝ (Fin 3)) :
  dist A C^2 + dist B D^2 + dist A D^2 + dist B C^2 ≥ dist A B^2 + dist C D^2 := by
  have h1 : dist A C = Real.sqrt (∑ i : Fin 3, (A i - C i) ^ 2) := by
    simp [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three]
  have h2 : dist B D = Real.sqrt (∑ i : Fin 3, (B i - D i) ^ 2) := by
    simp [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three]
  have h3 : dist A D = Real.sqrt (∑ i : Fin 3, (A i - D i) ^ 2) := by
    simp [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three]
  have h4 : dist B C = Real.sqrt (∑ i : Fin 3, (B i - C i) ^ 2) := by
    simp [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three]
  have h5 : dist A B = Real.sqrt (∑ i : Fin 3, (A i - B i) ^ 2) := by
    simp [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three]
  have h6 : dist C D = Real.sqrt (∑ i : Fin 3, (C i - D i) ^ 2) := by
    simp [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three]
  rw [h1, h2, h3, h4, h5, h6]
  have h13 : (∑ i : Fin 3, (A i - C i) ^ 2) + (∑ i : Fin 3, (B i - D i) ^ 2) + (∑ i : Fin 3, (A i - D i) ^ 2) + (∑ i : Fin 3, (B i - C i) ^ 2) ≥ (∑ i : Fin 3, (A i - B i) ^ 2) + (∑ i : Fin 3, (C i - D i) ^ 2) := by
    have h15 : (∑ i : Fin 3, (A i - C i) ^ 2) + (∑ i : Fin 3, (B i - D i) ^ 2) + (∑ i : Fin 3, (A i - D i) ^ 2) + (∑ i : Fin 3, (B i - C i) ^ 2) - ((∑ i : Fin 3, (A i - B i) ^ 2) + (∑ i : Fin 3, (C i - D i) ^ 2)) ≥ 0 := by
      have h16 : (∑ i : Fin 3, (A i - C i) ^ 2) + (∑ i : Fin 3, (B i - D i) ^ 2) + (∑ i : Fin 3, (A i - D i) ^ 2) + (∑ i : Fin 3, (B i - C i) ^ 2) - ((∑ i : Fin 3, (A i - B i) ^ 2) + (∑ i : Fin 3, (C i - D i) ^ 2)) = (∑ i : Fin 3, ((A i + B i - C i - D i) ^ 2)) := by
        simp [Finset.sum]
        all_goals ring
      rw [h16]
      have h14 : (∑ i : Fin 3, ((A i + B i - C i - D i) ^ 2)) ≥ 0 := by
        apply Finset.sum_nonneg
        intro i _
        positivity
      linarith
    linarith
  have h14 : Real.sqrt (∑ i : Fin 3, (A i - C i) ^ 2) ^ 2 = (∑ i : Fin 3, (A i - C i) ^ 2) := by
    rw [Real.sq_sqrt]
    positivity
  have h15 : Real.sqrt (∑ i : Fin 3, (B i - D i) ^ 2) ^ 2 = (∑ i : Fin 3, (B i - D i) ^ 2) := by
    rw [Real.sq_sqrt]
    positivity
  have h16 : Real.sqrt (∑ i : Fin 3, (A i - D i) ^ 2) ^ 2 = (∑ i : Fin 3, (A i - D i) ^ 2) := by
    rw [Real.sq_sqrt]
    positivity
  have h17 : Real.sqrt (∑ i : Fin 3, (B i - C i) ^ 2) ^ 2 = (∑ i : Fin 3, (B i - C i) ^ 2) := by
    rw [Real.sq_sqrt]
    positivity
  have h18 : Real.sqrt (∑ i : Fin 3, (A i - B i) ^ 2) ^ 2 = (∑ i : Fin 3, (A i - B i) ^ 2) := by
    rw [Real.sq_sqrt]
    positivity
  have h19 : Real.sqrt (∑ i : Fin 3, (C i - D i) ^ 2) ^ 2 = (∑ i : Fin 3, (C i - D i) ^ 2) := by
    rw [Real.sq_sqrt]
    positivity
  nlinarith [h13, h14, h15, h16, h17, h18, h19]