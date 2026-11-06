import Mathlib

open Real
open scoped BigOperators

theorem algebra_325901 {X Y : Fin 2 → ℝ}
  (hX : ∀ i, 2 ≤ X i ∧ X i ≤ 3)
  (hXY : ∀ i, X i * Y i = 1) :
  (∑ i, X i * (1 / 2)) * (∑ i, Y i * (1 / 2)) ≤ 25 / 24 := by

  have h1 : 2 ≤ X 0 := by 
    have h := hX 0
    linarith 

  have h2 : X 0 ≤ 3 := by 
    have h := hX 0
    linarith

  have h3 : 2 ≤ X 1 := by 
    have h := hX 1
    linarith

  have h4 : X 1 ≤ 3 := by 
    have h := hX 1
    linarith

  have h5 : X 0 * Y 0 = 1 := by
    apply hXY 0

  have h6 : X 1 * Y 1 = 1 := by 
    apply hXY 1

  have h7 : (∑ i : Fin 2, X i * (1 / 2)) = (X 0 + X 1) / 2 := by
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
    <;> ring

  have h8 : (∑ i : Fin 2, Y i * (1 / 2)) = (Y 0 + Y 1) / 2 := by 
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
    <;> ring

  rw [h7, h8]

  have h80 : Y 0 = 1 / X 0 := by
    have hne1 : X 0 ≠ 0 := by 
      linarith [h1, h2]
    field_simp [hne1] at *
    <;> nlinarith [h5]

  have h81 : Y 1 = 1 / X 1 := by
    have hne1 : X 1 ≠ 0 := by 
      linarith [h3, h4]
    field_simp [hne1] at *
    <;> nlinarith [h6]

  rw [h80, h81]
  have h13 : 0 < X 0 := by linarith 
  have h14 : 0 < X 1 := by linarith

  have h9 : X 0 ≥ 2 := h1
  have h10 : X 0 ≤ 3 := h2
  have h11 : X 1 ≥ 2 := h3
  have h12 : X 1 ≤ 3 := h4

  have h9' : X 0 * X 1 > 0 := mul_pos (by linarith) (by linarith)

  have h20 : (X 0 + X 1) ^ 2 / (4 * X 0 * X 1) ≤ (25 / 24) := by

    have h21 : (X 0 + X 1) ^ 2 ≤ (25 / 6) * (X 0 * X 1) := by
      nlinarith [sq_nonneg (X 0 - 2), sq_nonneg (X 1 - 3), sq_nonneg (X 0 - 3), sq_nonneg (X 1 - 2), 
        mul_nonneg (sub_nonneg.mpr h9) (sub_nonneg.mpr h10), 
        mul_nonneg (sub_nonneg.mpr h11) (sub_nonneg.mpr h12), 
        mul_nonneg (sub_nonneg.mpr h9) (sub_nonneg.mpr h11), 
        mul_nonneg (sub_nonneg.mpr h10) (sub_nonneg.mpr h12)
      ]
    
    have h22 : (X 0 + X 1) ^ 2 / (4 * X 0 * X 1) ≤ (25 / 24) := by
      have h17 : 0 < 4 * X 0 * X 1 := by 
        nlinarith [show X 0 > 0 by linarith, show X 1 > 0 by linarith]
      apply (div_le_iff₀ h17).mpr
      nlinarith [h21, mul_nonneg (sub_nonneg.mpr h9) (sub_nonneg.mpr h11), mul_nonneg (sub_nonneg.mpr h10) (sub_nonneg.mpr h12)]
    
    linarith [h22]

  have h21 : ((X 0 + X 1) / 2) * ((1 / X 0 + 1 / X 1) / 2) ≤ (25 / 24) := by 
    have h22 : ((X 0 + X 1) / 2) * ((1 / X 0 + 1 / X 1) / 2) = (X 0 + X 1) ^ 2 / (4 * X 0 * X 1) := by 
      field_simp 
      <;> ring 
    linarith [h22, h20]

  linarith [h21]