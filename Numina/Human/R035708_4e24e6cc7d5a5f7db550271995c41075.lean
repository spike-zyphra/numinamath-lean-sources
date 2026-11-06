import Mathlib

open Real Set
open scoped Real

theorem inequalities_309425 (A B C : Real) (hA : A ∈ Ioo 0 (π / 2)) (hB : B ∈ Ioo 0 (π / 2))
    (hC : C ∈ Ioo 0 (π / 2)) (hABC : A + B + C = π) :
    tan A * (cot B + cot C) + tan B * (cot C + cot A) + tan C * (cot A + cot B) ≥ 6 := by
  
 
  

  have h1 : 0 < A := hA.left
  have h2 : A < π / 2 := hA.right
  have h3 : 0 < B := hB.left
  have h4 : B < π / 2 := hB.right
  have h5 : 0 < C := hC.left
  have h6 : C < π / 2 := hC.right
  have htanA_pos : 0 < tan A := by apply tan_pos_of_pos_of_lt_pi_div_two; linarith; linarith
  have htanB_pos : 0 < tan B := by apply tan_pos_of_pos_of_lt_pi_div_two; linarith; linarith
  have htanC_pos : 0 < tan C := by apply tan_pos_of_pos_of_lt_pi_div_two; linarith; linarith
  have h1 : tan A * (cot B + cot C) + tan B * (cot C + cot A) + tan C * (cot A + cot B) =
      (tan A / tan B + tan A / tan C + tan B / tan C + tan B / tan A + tan C / tan A + tan C / tan B) := by
    have h1 : cot B = cos B / sin B := by rw [cot_eq_cos_div_sin]
    have h2 : cot C = cos C / sin C := by rw [cot_eq_cos_div_sin]
    have h3 : cot A = cos A / sin A := by rw [cot_eq_cos_div_sin]
    rw [h1, h2, h3]
    field_simp [tan_eq_sin_div_cos]
    <;> ring
  rw [h1]
  have h2 : tan A / tan B + tan B / tan A ≥ 2 := by
    have h_pos : 0 < tan A := htanA_pos
    have h_pos' : 0 < tan B := htanB_pos
    have h3 : tan A / tan B + tan B / tan A - 2 ≥ 0 := by
      have h4 : tan A / tan B + tan B / tan A - 2 = (tan A - tan B) ^ 2 / (tan A * tan B) := by
        field_simp
        ring
      rw [h4]
      have h5 : (tan A - tan B) ^ 2 ≥ 0 := sq_nonneg (tan A - tan B)
      have h6 : tan A * tan B > 0 := mul_pos h_pos h_pos'
      apply div_nonneg
      · linarith
      · nlinarith
    linarith
  have h3 : tan B / tan C + tan C / tan B ≥ 2 := by
    have h_pos : 0 < tan B := htanB_pos
    have h_pos' : 0 < tan C := htanC_pos
    have h3 : tan B / tan C + tan C / tan B - 2 ≥ 0 := by
      have h4 : tan B / tan C + tan C / tan B - 2 = (tan B - tan C) ^ 2 / (tan B * tan C) := by
        field_simp
        ring
      rw [h4]
      have h5 : (tan B - tan C) ^ 2 ≥ 0 := sq_nonneg (tan B - tan C)
      have h6 : tan B * tan C > 0 := mul_pos h_pos h_pos'
      apply div_nonneg
      · linarith
      · nlinarith
    linarith
  have h4 : tan C / tan A + tan A / tan C ≥ 2 := by
    have h_pos : 0 < tan C := htanC_pos
    have h_pos' : 0 < tan A := htanA_pos
    have h3 : tan C / tan A + tan A / tan C - 2 ≥ 0 := by
      have h4 : tan C / tan A + tan A / tan C - 2 = (tan C - tan A) ^ 2 / (tan C * tan A) := by
        field_simp
        ring
      rw [h4]
      have h5 : (tan C - tan A) ^ 2 ≥ 0 := sq_nonneg (tan C - tan A)
      have h6 : tan C * tan A > 0 := mul_pos h_pos h_pos'
      apply div_nonneg
      · linarith
      · nlinarith
    linarith
  nlinarith [h2, h3, h4]