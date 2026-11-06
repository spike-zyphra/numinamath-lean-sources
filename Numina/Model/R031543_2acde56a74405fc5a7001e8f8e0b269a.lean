import Mathlib

theorem algebra_186185 : Real.tan (255 * Real.pi / 180) - Real.tan (195 * Real.pi / 180) = 2 * Real.sqrt 3 := by
  have h1 : Real.tan (255 * Real.pi / 180) = Real.tan (5 * Real.pi / 12) := by
    have h2 : 255 * Real.pi / 180 = 5 * Real.pi / 12 + Real.pi := by
      linarith [Real.pi_pos]
    rw [h2]
    have htan_add_pi : ∀ x, Real.tan (x + Real.pi) = Real.tan x := by
      intro x
      rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]
      have h3 : Real.sin (x + Real.pi) = -Real.sin x := Real.sin_add_pi x
      have h4 : Real.cos (x + Real.pi) = -Real.cos x := Real.cos_add_pi x
      simp [h3, h4]
      <;> ring_nf
      <;> simp [Real.sin_pos_of_pos_of_lt_pi, Real.cos_pos_of_mem_Ioo, Real.sin_sq, Real.cos_sq]
      <;> ring
    specialize htan_add_pi (5 * Real.pi / 12)
    exact htan_add_pi
  have h4 : Real.tan (195 * Real.pi / 180) = Real.tan (Real.pi / 12) := by
    have h5 : 195 * Real.pi / 180 = Real.pi / 12 + Real.pi := by
      linarith [Real.pi_pos]
    rw [h5]
    have htan_add_pi : ∀ x, Real.tan (x + Real.pi) = Real.tan x := by
      intro x
      rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]
      have h3 : Real.sin (x + Real.pi) = -Real.sin x := Real.sin_add_pi x
      have h4 : Real.cos (x + Real.pi) = -Real.cos x := Real.cos_add_pi x
      simp [h3, h4]
      <;> ring_nf
      <;> simp [Real.sin_pos_of_pos_of_lt_pi, Real.cos_pos_of_mem_Ioo, Real.sin_sq, Real.cos_sq]
      <;> ring
    specialize htan_add_pi (Real.pi / 12)
    exact htan_add_pi
  rw [h1, h4]
  have h7 : Real.tan (5 * Real.pi / 12) = Real.cos (Real.pi / 12) / Real.sin (Real.pi / 12) := by
    have h8 : 5 * Real.pi / 12 = Real.pi / 2 - Real.pi / 12 := by
      linarith [Real.pi_pos]
    rw [h8]
    have h10 : Real.tan (Real.pi / 2 - Real.pi / 12) = Real.cos (Real.pi / 12) / Real.sin (Real.pi / 12) := by
      rw [Real.tan_eq_sin_div_cos]
      have h11 : Real.sin (Real.pi / 2 - Real.pi / 12) = Real.cos (Real.pi / 12) := by
        rw [Real.sin_pi_div_two_sub]
      have h12 : Real.cos (Real.pi / 2 - Real.pi / 12) = Real.sin (Real.pi / 12) := by
        rw [Real.cos_pi_div_two_sub]
      rw [h11, h12]
      <;> ring
    exact h10
  have htan : Real.tan (Real.pi / 12) = Real.sin (Real.pi / 12) / Real.cos (Real.pi / 12) := by
    rw [Real.tan_eq_sin_div_cos]
  rw [h7, htan]
  have hx1 : Real.sin (Real.pi / 12) > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have hx2 : Real.cos (Real.pi / 12) > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have hx3 : Real.sin (Real.pi / 12) * Real.cos (Real.pi / 12) ≠ 0 := by
    apply mul_ne_zero
    linarith [hx1]
    linarith [hx2]
  have hx4 : (Real.cos (Real.pi / 12)) / (Real.sin (Real.pi / 12)) - (Real.sin (Real.pi / 12) / Real.cos (Real.pi / 12)) =
    (Real.cos (Real.pi / 12) ^ 2 - Real.sin (Real.pi / 12) ^ 2) / (Real.sin (Real.pi / 12) * Real.cos (Real.pi / 12)) := by
    field_simp [hx1, hx2]
    <;> ring
  rw [hx4]
  have hx5 : Real.cos (Real.pi / 12) ^ 2 - Real.sin (Real.pi / 12) ^ 2 = Real.sqrt 3 / 2 := by
    have hcos2 : Real.cos (Real.pi / 12) ^ 2 - Real.sin (Real.pi / 12) ^ 2 = Real.cos (2 * (Real.pi / 12)) := by
      rw [Real.cos_two_mul, Real.sin_sq]
      ring
      <;> nlinarith
    rw [hcos2]
    have hcos2' : 2 * (Real.pi / 12) = Real.pi / 6 := by
      ring
    rw [hcos2']
    have hcospi6 : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := Real.cos_pi_div_six
    rw [hcospi6]
  have hx6 : Real.sin (Real.pi / 12) * Real.cos (Real.pi / 12) = 1 / 4 := by
    have hsin2x : Real.sin (Real.pi / 12) * Real.cos (Real.pi / 12) = (1 / 2) * Real.sin (2 * (Real.pi / 12)) := by
      rw [Real.sin_two_mul]
      <;> ring
    rw [hsin2x]
    have h2x : 2 * (Real.pi / 12) = Real.pi / 6 := by
      ring
    rw [h2x]
    have hsinpi6 : Real.sin (Real.pi / 6) = 1 / 2 := Real.sin_pi_div_six
    rw [hsinpi6]
    all_goals norm_num
  rw [hx5, hx6]
  <;> field_simp
  <;> ring
  all_goals nlinarith
  all_goals nlinarith
  all_goals nlinarith
  all_goals nlinarith