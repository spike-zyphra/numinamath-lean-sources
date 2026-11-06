import Mathlib
open Real Set

theorem algebra_4911 (x : Real) (hx : x ∈ Ioo 0 (π / 2)) (h : cos x = 15 / 17) :
    1 - 2 * sin x / (3 * tan x) = 7 / 17 := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : sin x > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h2 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  rw [h] at h2
  have h3 : sin x = 8 / 17 := by
    nlinarith [h1]
  have htan : tan x = sin x / cos x := by
    rw [Real.tan_eq_sin_div_cos]
  have htan_val : tan x = 8 / 15 := by
    rw [htan, h3, h]
    <;> norm_num
  rw [htan_val, h3]
  <;> field_simp [h]
  <;> norm_num
  <;> nlinarith
  <;> norm_num
  <;> linarith
  <;> norm_num
  all_goals linarith