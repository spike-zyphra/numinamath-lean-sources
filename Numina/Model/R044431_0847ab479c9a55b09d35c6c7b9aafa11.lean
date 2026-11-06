import Mathlib

open Real
open scoped BigOperators

theorem inequalities_110624 (A B C D : EuclideanSpace ℝ (Fin 2))
  (h : ¬Collinear ℝ {A, B, C} ∧ ¬Collinear ℝ {A, B, D} ∧
    ¬Collinear ℝ {A, C, D} ∧ ¬Collinear ℝ {B, C, D}) :
  dist A C^2 + dist B D^2 ≤ dist A B^2 + dist B C^2 + dist C D^2 + dist D A^2 := by
  have h1' : (dist A C) ^ 2 = (∑ i : Fin 2, (A i - C i) ^ 2) := by
    rw [show dist A C = Real.sqrt (∑ i : Fin 2, (A i - C i) ^ 2) by
      simp [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    ]
    rw [Real.sq_sqrt]
    positivity
  have h2' : (dist B D) ^ 2 = (∑ i : Fin 2, (B i - D i) ^ 2) := by
    rw [show dist B D = Real.sqrt (∑ i : Fin 2, (B i - D i) ^ 2) by
      simp [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    ]
    rw [Real.sq_sqrt]
    positivity
  have h3' : (dist A B) ^ 2 = (∑ i : Fin 2, (A i - B i) ^ 2) := by
    rw [show dist A B = Real.sqrt (∑ i : Fin 2, (A i - B i) ^ 2) by
      simp [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    ]
    rw [Real.sq_sqrt]
    positivity
  have h4' : (dist B C) ^ 2 = (∑ i : Fin 2, (B i - C i) ^ 2) := by
    rw [show dist B C = Real.sqrt (∑ i : Fin 2, (B i - C i) ^ 2) by
      simp [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    ]
    rw [Real.sq_sqrt]
    positivity
  have h5' : (dist C D) ^ 2 = (∑ i : Fin 2, (C i - D i) ^ 2) := by
    rw [show dist C D = Real.sqrt (∑ i : Fin 2, (C i - D i) ^ 2) by
      simp [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    ]
    rw [Real.sq_sqrt]
    positivity
  have h6' : (dist D A) ^ 2 = (∑ i : Fin 2, (D i - A i) ^ 2) := by
    rw [show dist D A = Real.sqrt (∑ i : Fin 2, (D i - A i) ^ 2) by
      simp [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    ]
    rw [Real.sq_sqrt]
    positivity
  rw [h1', h2', h3', h4', h5', h6']
  have h7 {i : Fin 2} : (A i - C i) ^ 2 + (B i - D i) ^ 2 ≤ (A i - B i) ^ 2 + (B i - C i) ^ 2 + (C i - D i) ^ 2 + (D i - A i) ^ 2 := by
    have h8 : (A i - B i) ^ 2 + (B i - C i) ^ 2 + (C i - D i) ^ 2 + (D i - A i) ^ 2 - ((A i - C i) ^ 2 + (B i - D i) ^ 2) ≥ 0 := by
      have h9 : (A i - B i) ^ 2 + (B i - C i) ^ 2 + (C i - D i) ^ 2 + (D i - A i) ^ 2 - ((A i - C i) ^ 2 + (B i - D i) ^ 2) = (A i - B i + C i - D i) ^ 2 := by
        ring
      rw [h9]
      apply sq_nonneg
    linarith
  have h8 : ∑ i : Fin 2, ((A i - C i) ^ 2 + (B i - D i) ^ 2) ≤ ∑ i : Fin 2, ((A i - B i) ^ 2 + (B i - C i) ^ 2 + (C i - D i) ^ 2 + (D i - A i) ^ 2) := by
    apply Finset.sum_le_sum
    intro i hi
    have h7_i : (A i - C i) ^ 2 + (B i - D i) ^ 2 ≤ (A i - B i) ^ 2 + (B i - C i) ^ 2 + (C i - D i) ^ 2 + (D i - A i) ^ 2 := h7
    linarith
  have h9 : ∑ i : Fin 2, ((A i - C i) ^ 2 + (B i - D i) ^ 2) =
      (∑ i : Fin 2, (A i - C i) ^ 2) + (∑ i : Fin 2, (B i - D i) ^ 2) := by
    simp [Finset.sum_add_distrib]
  have h10 : ∑ i : Fin 2, ((A i - B i) ^ 2 + (B i - C i) ^ 2 + (C i - D i) ^ 2 + (D i - A i) ^ 2) =
      (∑ i : Fin 2, (A i - B i) ^ 2) + (∑ i : Fin 2, (B i - C i) ^ 2) + (∑ i : Fin 2, (C i - D i) ^ 2) + (∑ i : Fin 2, (D i - A i) ^ 2) := by
    simp [Finset.sum_add_distrib]
  linarith [h8, h9, h10]