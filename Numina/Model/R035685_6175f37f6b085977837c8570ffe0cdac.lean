import Mathlib

open Real
open scoped BigOperators

theorem inequalities_603895 (A B C D P Q R S : EuclideanSpace ℝ (Fin 2))
  (h₀ : ¬Collinear ℝ {A, B, C})
  (h₁ : ¬Collinear ℝ {B, C, D})
  (h₂ : ¬Collinear ℝ {C, D, A})
  (h₃ : ¬Collinear ℝ {D, A, B})
  (h₄ : P = midpoint ℝ B C)
  (h₅ : Q = midpoint ℝ C D)
  (h₆ : R = midpoint ℝ D A)
  (h₇ : S = midpoint ℝ A B) :
  4 * (dist A P ^ 2 + dist B Q ^ 2 + dist C R ^ 2 + dist D S ^ 2) ≤
  5 * (dist A B ^ 2 + dist B C ^ 2 + dist C D ^ 2 + dist D A ^ 2) := by
  rw [h₄] at *
  rw [h₅] at *
  rw [h₆] at *
  rw [h₇] at *
  have h1 : dist A (midpoint ℝ B C) = Real.sqrt (∑ i : Fin 2, (A i - (B i + C i) / 2) ^ 2) := by
    simp [dist_eq_norm, EuclideanSpace.norm_eq, midpoint_eq_smul_add]
    all_goals
      ring_nf
  have h2 : dist B (midpoint ℝ C D) = Real.sqrt (∑ i : Fin 2, (B i - (C i + D i) / 2) ^ 2) := by
    simp [dist_eq_norm, EuclideanSpace.norm_eq, midpoint_eq_smul_add]
    all_goals
      ring_nf
  have h3 : dist C (midpoint ℝ D A) = Real.sqrt (∑ i : Fin 2, (C i - (D i + A i) / 2) ^ 2) := by
    simp [dist_eq_norm, EuclideanSpace.norm_eq, midpoint_eq_smul_add]
    all_goals
      ring_nf
  have h4 : dist D (midpoint ℝ A B) = Real.sqrt (∑ i : Fin 2, (D i - (A i + B i) / 2) ^ 2) := by
    simp [dist_eq_norm, EuclideanSpace.norm_eq, midpoint_eq_smul_add]
    all_goals
      ring_nf
  have h5 : dist A B = Real.sqrt (∑ i : Fin 2, (A i - B i) ^ 2) := by
    simp [dist_eq_norm, EuclideanSpace.norm_eq]
  have h6 : dist B C = Real.sqrt (∑ i : Fin 2, (B i - C i) ^ 2) := by
    simp [dist_eq_norm, EuclideanSpace.norm_eq]
  have h7 : dist C D = Real.sqrt (∑ i : Fin 2, (C i - D i) ^ 2) := by
    simp [dist_eq_norm, EuclideanSpace.norm_eq]
  have h8 : dist D A = Real.sqrt (∑ i : Fin 2, (D i - A i) ^ 2) := by
    simp [dist_eq_norm, EuclideanSpace.norm_eq]
  rw [h1, h2, h3, h4, h5, h6, h7, h8]
  have h9 : 4 * (∑ i : Fin 2, (A i - (B i + C i) / 2) ^ 2 + ∑ i : Fin 2, (B i - (C i + D i) / 2) ^ 2 + ∑ i : Fin 2, (C i - (D i + A i) / 2) ^ 2 + ∑ i : Fin 2, (D i - (A i + B i) / 2) ^ 2) ≤ 5 * (∑ i : Fin 2, (A i - B i) ^ 2 + ∑ i : Fin 2, (B i - C i) ^ 2 + ∑ i : Fin 2, (C i - D i) ^ 2 + ∑ i : Fin 2, (D i - A i) ^ 2) := by
    have h10 : ∀ i : Fin 2, 4 * ((A i - (B i + C i) / 2) ^ 2 + (B i - (C i + D i) / 2) ^ 2 + (C i - (D i + A i) / 2) ^ 2 + (D i - (A i + B i) / 2) ^ 2) ≤ 5 * ((A i - B i) ^ 2 + (B i - C i) ^ 2 + (C i - D i) ^ 2 + (D i - A i) ^ 2) := by
      intro i
      have h11 : 4 * ((A i - (B i + C i) / 2) ^ 2 + (B i - (C i + D i) / 2) ^ 2 + (C i - (D i + A i) / 2) ^ 2 + (D i - (A i + B i) / 2) ^ 2) ≤ 5 * ((A i - B i) ^ 2 + (B i - C i) ^ 2 + (C i - D i) ^ 2 + (D i - A i) ^ 2) := by
        nlinarith [sq_nonneg (A i + B i - C i - D i), sq_nonneg (A i - B i + C i - D i), sq_nonneg (A i - B i - C i + D i), sq_nonneg (A i + B i + C i + D i), sq_nonneg (A i - C i), sq_nonneg (B i - D i)]
      linarith
    have h12 : ∑ i : Fin 2, (4 * ((A i - (B i + C i) / 2) ^ 2 + (B i - (C i + D i) / 2) ^ 2 + (C i - (D i + A i) / 2) ^ 2 + (D i - (A i + B i) / 2) ^ 2)) ≤ ∑ i : Fin 2, (5 * ((A i - B i) ^ 2 + (B i - C i) ^ 2 + (C i - D i) ^ 2 + (D i - A i) ^ 2)) := by
      apply Finset.sum_le_sum
      intro i hi
      specialize h10 i
      linarith
    simp [Finset.sum_mul] at h12 ⊢
    linarith
  have h14 : 4 * ((Real.sqrt (∑ i : Fin 2, (A i - (B i + C i) / 2) ^ 2)) ^ 2 + (Real.sqrt (∑ i : Fin 2, (B i - (C i + D i) / 2) ^ 2)) ^ 2 + (Real.sqrt (∑ i : Fin 2, (C i - (D i + A i) / 2) ^ 2)) ^ 2 + (Real.sqrt (∑ i : Fin 2, (D i - (A i + B i) / 2) ^ 2)) ^ 2) ≤ 5 * ((Real.sqrt (∑ i : Fin 2, (A i - B i) ^ 2)) ^ 2 + (Real.sqrt (∑ i : Fin 2, (B i - C i) ^ 2)) ^ 2 + (Real.sqrt (∑ i : Fin 2, (C i - D i) ^ 2)) ^ 2 + (Real.sqrt (∑ i : Fin 2, (D i - A i) ^ 2)) ^ 2) := by
    have h15 : (Real.sqrt (∑ i : Fin 2, (A i - (B i + C i) / 2) ^ 2)) ^ 2 = ∑ i : Fin 2, (A i - (B i + C i) / 2) ^ 2 := by
      rw [Real.sq_sqrt]
      positivity
    have h16 : (Real.sqrt (∑ i : Fin 2, (B i - (C i + D i) / 2) ^ 2)) ^ 2 = ∑ i : Fin 2, (B i - (C i + D i) / 2) ^ 2 := by
      rw [Real.sq_sqrt]
      positivity
    have h17 : (Real.sqrt (∑ i : Fin 2, (C i - (D i + A i) / 2) ^ 2)) ^ 2 = ∑ i : Fin 2, (C i - (D i + A i) / 2) ^ 2 := by
      rw [Real.sq_sqrt]
      positivity
    have h18 : (Real.sqrt (∑ i : Fin 2, (D i - (A i + B i) / 2) ^ 2)) ^ 2 = ∑ i : Fin 2, (D i - (A i + B i) / 2) ^ 2 := by
      rw [Real.sq_sqrt]
      positivity
    have h19 : (Real.sqrt (∑ i : Fin 2, (A i - B i) ^ 2)) ^ 2 = ∑ i : Fin 2, (A i - B i) ^ 2 := by
      rw [Real.sq_sqrt]
      positivity
    have h20 : (Real.sqrt (∑ i : Fin 2, (B i - C i) ^ 2)) ^ 2 = ∑ i : Fin 2, (B i - C i) ^ 2 := by
      rw [Real.sq_sqrt]
      positivity
    have h21 : (Real.sqrt (∑ i : Fin 2, (C i - D i) ^ 2)) ^ 2 = ∑ i : Fin 2, (C i - D i) ^ 2 := by
      rw [Real.sq_sqrt]
      positivity
    have h22 : (Real.sqrt (∑ i : Fin 2, (D i - A i) ^ 2)) ^ 2 = ∑ i : Fin 2, (D i - A i) ^ 2 := by
      rw [Real.sq_sqrt]
      positivity
    rw [h15, h16, h17, h18, h19, h20, h21, h22]
    linarith [h9]
  nlinarith [h9]