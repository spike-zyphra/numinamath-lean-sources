import Mathlib

open Real
open scoped BigOperators

theorem inequalities_208872 (a b c d : EuclideanSpace ℝ (Fin 3))
  (h₀ : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) :
  (dist a b)^2 + (dist c d)^2 ≤ (dist a c)^2 + (dist a d)^2 + (dist b c)^2 + (dist b d)^2 := by
  have h1 : (dist a b) ^ 2 = (a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 + (a 2 - b 2) ^ 2 := by
    have h2 : (dist a b) = Real.sqrt ((a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 + (a 2 - b 2) ^ 2) := by
      simp [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three]
      <;> ring
    rw [h2]
    rw [Real.sq_sqrt (by positivity)]
  have h2 : (dist a c) ^ 2 = (a 0 - c 0) ^ 2 + (a 1 - c 1) ^ 2 + (a 2 - c 2) ^ 2 := by
    have h3 : (dist a c) = Real.sqrt ((a 0 - c 0) ^ 2 + (a 1 - c 1) ^ 2 + (a 2 - c 2) ^ 2) := by
      simp [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three]
      <;> ring 
    rw [h3]
    rw [Real.sq_sqrt (by positivity)]
  have h3 : (dist a d) ^ 2 = (a 0 - d 0) ^ 2 + (a 1 - d 1) ^ 2 + (a 2 - d 2) ^ 2 := by 
    have h4 : (dist a d) = Real.sqrt ((a 0 - d 0) ^ 2 + (a 1 - d 1) ^ 2 + (a 2 - d 2) ^ 2) := by
      simp [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three]
      <;> ring
    rw [h4]
    rw [Real.sq_sqrt (by positivity)]
  have h4 : (dist b c) ^ 2 = (b 0 - c 0) ^ 2 + (b 1 - c 1) ^ 2 + (b 2 - c 2) ^ 2 := by
    have h5 : (dist b c) = Real.sqrt ((b 0 - c 0) ^ 2 + (b 1 - c 1) ^ 2 + (b 2 - c 2) ^ 2) := by
      simp [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three]
      <;> ring
    rw [h5]
    rw [Real.sq_sqrt (by positivity)]
  have h5 : (dist b d) ^ 2 = (b 0 - d 0) ^ 2 + (b 1 - d 1) ^ 2 + (b 2 - d 2) ^ 2 := by
    have h6 : (dist b d) = Real.sqrt ((b 0 - d 0) ^ 2 + (b 1 - d 1) ^ 2 + (b 2 - d 2) ^ 2) := by
      simp [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three]
      <;> ring
    rw [h6]
    rw [Real.sq_sqrt (by positivity)]
  have h6 : (dist c d) ^ 2 = (c 0 - d 0) ^ 2 + (c 1 - d 1) ^ 2 + (c 2 - d 2) ^ 2 := by
    have h7 : (dist c d) = Real.sqrt ((c 0 - d 0) ^ 2 + (c 1 - d 1) ^ 2 + (c 2 - d 2) ^ 2) := by
      simp [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three]
      <;> ring
    rw [h7]
    rw [Real.sq_sqrt (by positivity)]
  rw [h1, h2, h3, h4, h5, h6]
  nlinarith [sq_nonneg (a 0 - b 0 - c 0 + d 0), sq_nonneg (a 1 - b 1 - c 1 + d 1), sq_nonneg (a 2 - b 2 - c 2 + d 2),
      sq_nonneg (a 0 - b 0 + c 0 - d 0), sq_nonneg (a 1 - b 1 + c 1 - d 1), sq_nonneg (a 2 - b 2 + c 2 - d 2),
      sq_nonneg (a 0 + b 0 - c 0 - d 0), sq_nonneg (a 1 + b 1 - c 1 - d 1), sq_nonneg (a 2 + b 2 - c 2 - d 2),
      sq_nonneg (a 0 - b 0 - c 0 + d 0), sq_nonneg (a 1 - b 1 - c 1 + d 1), sq_nonneg (a 2 - b 2 - c 2 + d 2)]