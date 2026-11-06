import Mathlib

open Real
open scoped BigOperators

theorem inequalities_602479
  (A B C D : EuclideanSpace ℝ (Fin 3)) :
  dist A C^2 + dist B D^2 + dist A D^2 + dist B C^2 ≥
  dist A B^2 + dist C D^2 := by
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
  have h7 : (∑ i : Fin 3, (A i - C i) ^ 2) ≥ 0 := by positivity
  have h8 : (∑ i : Fin 3, (B i - D i) ^ 2) ≥ 0 := by positivity
  have h9 : (∑ i : Fin 3, (A i - D i) ^ 2) ≥ 0 := by positivity
  have h10 : (∑ i : Fin 3, (B i - C i) ^ 2) ≥ 0 := by positivity
  have h11 : (∑ i : Fin 3, (A i - B i) ^ 2) ≥ 0 := by positivity
  have h12 : (∑ i : Fin 3, (C i - D i) ^ 2) ≥ 0 := by positivity
  have h14 : Real.sqrt (∑ i : Fin 3, (A i - C i) ^ 2) ^2 = (∑ i : Fin 3, (A i - C i) ^ 2) := by 
    rw [Real.sq_sqrt]
    linarith
  have h15 : Real.sqrt (∑ i : Fin 3, (B i - D i) ^ 2) ^2 = (∑ i : Fin 3, (B i - D i) ^ 2) := by 
    rw [Real.sq_sqrt]
    linarith
  have h16 : Real.sqrt (∑ i : Fin 3, (A i - D i) ^ 2) ^2 = (∑ i : Fin 3, (A i - D i) ^ 2) := by 
    rw [Real.sq_sqrt]
    linarith
  have h17 : Real.sqrt (∑ i : Fin 3, (B i - C i) ^ 2) ^2 = (∑ i : Fin 3, (B i - C i) ^ 2) := by 
    rw [Real.sq_sqrt]
    linarith
  have h18 : Real.sqrt (∑ i : Fin 3, (A i - B i) ^ 2) ^2 = (∑ i : Fin 3, (A i - B i) ^ 2) := by 
    rw [Real.sq_sqrt]
    linarith
  have h19 : Real.sqrt (∑ i : Fin 3, (C i - D i) ^ 2) ^2 = (∑ i : Fin 3, (C i - D i) ^ 2) := by 
    rw [Real.sq_sqrt]
    linarith
  have h13 : (∑ i : Fin 3, (A i - C i) ^ 2) + (∑ i : Fin 3, (B i - D i) ^ 2) + (∑ i : Fin 3, (A i - D i) ^ 2) + (∑ i : Fin 3, (B i - C i) ^ 2) ≥ (∑ i : Fin 3, (A i - B i) ^ 2) + (∑ i : Fin 3, (C i - D i) ^ 2) := by 
    have h14 : (∑ i : Fin 3, (A i - C i) ^ 2) + (∑ i : Fin 3, (B i - D i) ^ 2) + (∑ i : Fin 3, (A i - D i) ^ 2) + (∑ i : Fin 3, (B i - C i) ^ 2) =
      ∑ i : Fin 3, ((A i - C i) ^ 2 + (B i - D i) ^ 2 + (A i - D i) ^ 2 + (B i - C i) ^ 2) := by 
      simp [Finset.sum_add_distrib]
    have h15 : (∑ i : Fin 3, (A i - B i) ^ 2) + (∑ i : Fin 3, (C i - D i) ^ 2) = ∑ i : Fin 3, ((A i - B i) ^ 2 + (C i - D i) ^ 2) := by 
      simp [Finset.sum_add_distrib]
    rw [h14, h15]
    have h16 : ∀ i : Fin 3, ((A i - C i) ^ 2 + (B i - D i) ^ 2 + (A i - D i) ^ 2 + (B i - C i) ^ 2) ≥ ((A i - B i) ^ 2 + (C i - D i) ^ 2) := by
      intro i
      have h17 : (A i - C i) ^ 2 + (B i - D i) ^ 2 + (A i - D i) ^ 2 + (B i - C i) ^ 2 ≥ (A i - B i) ^ 2 + (C i - D i) ^ 2 := by 
        nlinarith [sq_nonneg (A i - B i - (C i - D i)), sq_nonneg (A i + B i - C i - D i), sq_nonneg (A i - D i - (B i - C i)), sq_nonneg (A i + D i - (B i + C i))]
      linarith
    apply Finset.sum_le_sum 
    intro i hi 
    specialize h16 i 
    linarith 
  nlinarith