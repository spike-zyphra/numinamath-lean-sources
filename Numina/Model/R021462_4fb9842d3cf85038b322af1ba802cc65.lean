import Mathlib

open Real
open scoped BigOperators

theorem inequalities_266618 (A B C D : EuclideanSpace ℝ (Fin 3)) :
  (dist A C)^2 + (dist B D)^2 + (dist A D)^2 + (dist B C)^2 ≥
  (dist A B)^2 + (dist C D)^2 := by
  have h1 : dist A C = Real.sqrt (∑ i : Fin 3, (A i - C i) ^ 2) := by
    simp [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three]
    all_goals norm_num
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
  have h7 : Real.sqrt (∑ i : Fin 3, (A i - C i) ^ 2) ^ 2 = ∑ i : Fin 3, (A i - C i) ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  have h8 : Real.sqrt (∑ i : Fin 3, (B i - D i) ^ 2) ^ 2 = ∑ i : Fin 3, (B i - D i) ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  have h9 : Real.sqrt (∑ i : Fin 3, (A i - D i) ^ 2) ^ 2 = ∑ i : Fin 3, (A i - D i) ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  have h10 : Real.sqrt (∑ i : Fin 3, (B i - C i) ^ 2) ^ 2 = ∑ i : Fin 3, (B i - C i) ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  have h11 : Real.sqrt (∑ i : Fin 3, (A i - B i) ^ 2) ^ 2 = ∑ i : Fin 3, (A i - B i) ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  have h12 : Real.sqrt (∑ i : Fin 3, (C i - D i) ^ 2) ^ 2 = ∑ i : Fin 3, (C i - D i) ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  rw [h7, h8, h9, h10, h11, h12]
  have h13 : ∑ i : Fin 3, (A i - C i) ^ 2 + ∑ i : Fin 3, (B i - D i) ^ 2 + ∑ i : Fin 3, (A i - D i) ^ 2 + ∑ i : Fin 3, (B i - C i) ^ 2 ≥ ∑ i : Fin 3, (A i - B i) ^ 2 + ∑ i : Fin 3, (C i - D i) ^ 2 := by
    have h17 : ∑ i : Fin 3, ((A i + B i - C i - D i : ℝ) ^ 2) ≥ 0 := by
      positivity
    simp [Finset.sum] at h17 ⊢
    linarith
  linarith