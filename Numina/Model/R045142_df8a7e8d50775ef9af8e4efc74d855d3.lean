import Mathlib

theorem algebra_10699 (O : EuclideanSpace ℝ (Fin 2)) (hO : O = 0)
    (C : Set (EuclideanSpace ℝ (Fin 2))) (hC : C = {P | P 0 ^ 2 - 24 * P 0 + P 1 ^ 2 + 10 * P 1 + 160 = 0}) :
    IsLeast {d | ∃ P ∈ C, d = dist O P} 10 := by
  constructor 
  · -- Show 10 is in the set
    use ![120 / 13, -50 / 13]
    constructor 
    · -- Show that the point is in C
      rw [hC]
      simp
      norm_num 
    · -- Show that the distance is 10 
      rw [hO]
      simp [dist_eq_norm, EuclideanSpace.norm_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      have h2 : ((120 / 13 : ℝ) ^ 2 + (-50 / 13 : ℝ) ^ 2) = (100 : ℝ) := by 
        norm_num
      rw [h2]
      have h3 : Real.sqrt ((100 : ℝ)) = (10 : ℝ) := by 
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num 
      rw [h3]
      all_goals norm_num 
  · -- Show 10 is minimal
    intro d 
    rintro ⟨P, hP, rfl⟩ 
    rw [hC] at hP 
    simp at hP 
    rw [hO]
    simp [dist_eq_norm, EuclideanSpace.norm_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] 
    have h1 : (P 0 - 12) ^ 2 + (P 1 + 5) ^ 2 = 9 := by 
      nlinarith 
    have h2 : (P 0) ^ 2 + (P 1) ^ 2 ≥ 100 := by
      nlinarith [sq_nonneg (P 0 - 120 / 13), sq_nonneg (P 1 + 50 / 13), sq_nonneg (13 * (P 0) - 120 * 13), sq_nonneg (13 * (P 1) + 50 * 13)]
    have h3 : Real.sqrt ((P 0) ^ 2 + (P 1) ^ 2) ≥ Real.sqrt (100 : ℝ) := Real.sqrt_le_sqrt (h2)
    have h4 : Real.sqrt (100 : ℝ) = (10 : ℝ) := by 
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num 
    linarith