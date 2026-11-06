import Mathlib

open Real Set
open scoped Real

theorem inequalities_245430 (x : Real) (hx : 0 ≤ x ∧ x < π / 2) :
    sin x ≥ tan x - 1 / 2 * tan x ^ 3 := by
  rcases hx with ⟨hx0, hx1⟩
  have hsin : sin x ≥ 0 := by
    apply sin_nonneg_of_nonneg_of_le_pi
    linarith [hx0, Real.pi_pos]
    linarith [hx0, Real.pi_pos]
  have hcos_pos : cos x > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [hx0, Real.pi_pos]
    linarith [hx0, Real.pi_pos]
  have htan : tan x = sin x / cos x := by
    rw [tan_eq_sin_div_cos]
  rw [htan]
  have hpos : cos x > 0 := hcos_pos
  have h1 : sin x * cos x ^ 3 ≥ (sin x / cos x - 1 / 2 * (sin x / cos x) ^ 3) * cos x ^ 3 := by
    have h3 : (sin x / cos x - 1 / 2 * (sin x / cos x) ^ 3) * cos x ^ 3 =
        sin x * cos x ^ 2 - 1 / 2 * sin x ^ 3 := by
      field_simp [hpos]
      <;> ring 
    rw [h3]
    have h2 : 0 ≤ cos x := by linarith
    have h4 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    have h5 : sin x * cos x ^ 3 ≥ sin x * cos x ^ 2 - 1 / 2 * sin x ^ 3 := by
      nlinarith [sq_nonneg (sin x - 0), sq_nonneg (cos x - 1 / 2), sq_nonneg (cos x - 1), sq_nonneg (sin x ^ 2 - 1 / 2), sq_nonneg ((sin x ) * (sin x - 0)), sq_nonneg ((cos x) * (sin x - 0)), sq_nonneg ((cos x) - 1), 
        mul_nonneg (show 0 ≤ sin x by linarith) (show 0 ≤ cos x by nlinarith), 
        sq_nonneg (sin x * (sin x - 0)), sq_nonneg ((sin x) * (cos x - 1)), sq_nonneg ((cos x) * (sin x - 0)), Real.sin_sq_add_cos_sq x
      ]
    linarith
  have h2 : 0 < cos x := hcos_pos
  have h7 : sin x - (sin x / cos x - 1 / 2 * (sin x / cos x) ^ 3) ≥ 0 := by
    have h8 : sin x - (sin x / cos x - 1 / 2 * (sin x / cos x) ^ 3) =
        (sin x * cos x ^ 3 - (sin x / cos x - 1 / 2 * (sin x / cos x) ^ 3) * cos x ^ 3) / cos x ^ 3 := by 
      field_simp [hcos_pos]
      <;> ring
    rw [h8]
    apply div_nonneg
    nlinarith [show 0 < cos x from h2, sq_nonneg (sin x * (sin x * sin x / 1) / cos x * sin x), sq_nonneg ((sin x) * (sin x)), sq_nonneg (sin x - 0), sq_nonneg (cos x * (sin x) / sin x * (sin x) * sin x) ]
    all_goals positivity
  linarith