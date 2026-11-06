import Mathlib

open Real Set

theorem algebra_119663 {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x ∧ x < π/2)
  (h : tan x = 3 * tan y) :
  x - y ≤ π/6 := by
  have h1 : 0 ≤ y := hy
  have h2 : y ≤ x := hxy.1
  have h3 : x < π / 2 := hxy.2
  have h4 : 0 ≤ x := by linarith
  have h8 : y < π / 2 := by
    nlinarith
  have h7 : 0 ≤ tan y := by
    apply tan_nonneg_of_nonneg_of_le_pi_div_two
    · linarith
    · linarith
  have h7x : 0 ≤ tan x := by
    apply tan_nonneg_of_nonneg_of_le_pi_div_two
    · linarith
    · linarith
  have hk2 : tan (x - y) = (tan x - tan y) / (1 + tan x * tan y) := by
    rw [Real.tan_eq_sin_div_cos]
    have hk5 : sin (x - y) = sin x * cos y - cos x * sin y := by
      rw [Real.sin_sub]
    have hk6 : cos (x - y) = cos x * cos y + sin x * sin y := by
      rw [Real.cos_sub]
    have hk0 : cos x > 0 := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · linarith [h4, h3]
      · linarith [h4, h3]
    have hk28 : cos y > 0 := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · linarith [h1, h8]
      · linarith [h1, h8]
    have hk7 : tan x = sin x / cos x := by rw [Real.tan_eq_sin_div_cos]
    have hk8 : tan y = sin y / cos y := by rw [Real.tan_eq_sin_div_cos]
    rw [hk7, hk8]
    field_simp [show cos x ≠ 0 by linarith, show cos y ≠ 0 by linarith]
    <;> rw [hk5, hk6]
  have hk10 : tan (x - y) ≤ Real.sqrt 3 / 3 := by
    have hk3 : tan (x - y) = (tan x - tan y) / (1 + tan x * tan y) := hk2
    rw [hk3]
    rw [show tan x = 3 * tan y by linarith [h]]
    have hk11 : tan y ≥ 0 := by linarith [h7]
    have hk13 : (3 * tan y - tan y) / (1 + (3 * tan y) * tan y) = (2 * tan y) / (1 + 3 * tan y ^ 2) := by
      ring_nf
    rw [hk13]
    have hk15 : (2 * tan y) / (1 + 3 * tan y ^ 2) ≤ Real.sqrt 3 / 3 := by
      have hk11 : tan y ≥ 0 := by linarith [h7]
      have hk16 : Real.sqrt 3 > 0 := by positivity
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg (tan y - Real.sqrt 3 / 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
        sq_nonneg (tan y), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), sq_nonneg (tan y ^ 2 - 1 / 3)
      ]
    linarith
  have hk12 : x - y ≤ Real.arctan (Real.sqrt 3 / 3) := by
    have hk22 : Real.tan (x - y) ≤ Real.sqrt 3 / 3 := hk10
    have hk24 : x - y ≥ 0 := by linarith
    have hk13 : x - y < Real.pi / 2 := by
      nlinarith [Real.pi_pos]
    have hk16 : Real.arctan (Real.tan (x - y)) = x - y := by
      rw [Real.arctan_tan]
      all_goals
      linarith [Real.pi_pos]
    have hk20 : Real.arctan (Real.tan (x - y)) ≤ Real.arctan (Real.sqrt 3 / 3) := by
      apply Real.arctan_le_arctan
      linarith
    linarith
  have hk22 : Real.arctan (Real.sqrt 3 / 3) = Real.pi / 6 := by
    have hk23 : Real.sqrt 3 / 3 = 1 / Real.sqrt 3 := by
      field_simp
    rw [hk23]
    have hk24 : Real.arctan (1 / Real.sqrt 3) = Real.pi / 6 := by
      have h11 : Real.tan (Real.pi / 6) = 1 / Real.sqrt 3 := by
        rw [Real.tan_pi_div_six]
      rw [← h11]
      apply Real.arctan_tan
      all_goals
      linarith [Real.pi_pos]
    exact hk24
  linarith