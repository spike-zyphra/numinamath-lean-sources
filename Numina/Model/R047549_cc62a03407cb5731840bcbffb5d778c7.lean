import Mathlib
open Real Set

theorem inequality_606436 (x : ℝ) (xs : x ∈ Ioo 0 (Real.pi / 2)):
(cos x) ^ 2 * cot x + (sin x) ^ 2 * tan x ≥ 1 := by
  rcases xs with ⟨hx1, hx2⟩
  have h1 : sin x > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_gt_31415, hx1, hx2]
    linarith [Real.pi_gt_31415, hx1, hx2]
  have h2 : cos x > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_gt_31415, hx1, hx2]
  have h3 : cot x = cos x / sin x := by
    rw [cot_eq_cos_div_sin]
  have h4 : tan x = sin x / cos x := by
    rw [tan_eq_sin_div_cos]
  rw [h3, h4]
  have hx3 : sin x > 0 := h1
  have hx4 : cos x > 0 := h2
  have h5 : (cos x) ^ 2 * (cos x / sin x) + (sin x) ^ 2 * (sin x / cos x) - 1 ≥ 0 := by
    have h6 : (cos x) ^ 2 * (cos x / sin x) + (sin x) ^ 2 * (sin x / cos x) - 1 =
        ( (cos x) ^ 4 + (sin x) ^ 4 - (sin x) * (cos x) ) / ( (sin x) * (cos x) ) := by
      field_simp
      ring
    rw [h6] at *
    apply div_nonneg
    nlinarith [sq_nonneg ( (cos x) ^ 2 - (sin x) ^ 2 ), sq_nonneg ( (cos x) - (sin x) ), sq_nonneg ( (cos x) ^ 2 + (sin x) ^ 2 - 1 ), sq_nonneg ( (cos x) - (sin x) ), sq_nonneg ( (cos x) * (sin x) - 1 / 2 ), Real.sin_sq_add_cos_sq x, mul_pos hx3 hx4 ]
    all_goals nlinarith [Real.sin_sq_add_cos_sq x, mul_pos hx3 hx4 ]
  linarith