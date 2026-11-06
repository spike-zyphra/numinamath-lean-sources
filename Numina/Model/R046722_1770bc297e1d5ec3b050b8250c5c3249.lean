import Mathlib

open Real Set
open scoped Real

theorem algebra_243236 {x y : ℝ} (hx : x ∈ Ioo 0 (π/2)) (hy : y ∈ Ioo 0 (π/2))
    (h1 : cos x / cos y = 2 * (cos y)^2) (h2 : sin x / sin y = 2 * (sin y)^2) :
    x = π/4 ∧ y = π/4 := by
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with  ⟨hy1, hy2⟩
  have hcosy : cos y > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith [hy1, Real.pi_pos]
    · linarith [hy2, Real.pi_pos]
  have hsiny : sin y > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    · linarith [hy1, Real.pi_pos]
    · linarith [hy2, Real.pi_pos, Real.pi_gt_three]
  have heq1 : cos x = 2 * (cos y)^3 := by
    have h : cos y > 0 := hcosy
    have hne : cos y ≠ 0 := by linarith
    field_simp [hne] at h1
    nlinarith
  have heq2 : sin x = 2 * (sin y)^3 := by
    have h : sin y > 0 := hsiny
    have hne : sin y ≠ 0 := by linarith
    field_simp [hne] at h2
    nlinarith
  have heq3 : cos x ^2 + sin x ^2 = 1 := by
    exact Real.cos_sq_add_sin_sq x
  have heq4 : 4 * ((cos y)^6 + (sin y)^6) = 1 := by
    rw [heq1, heq2] at heq3
    nlinarith [sq_pos_of_pos hcosy, sq_pos_of_pos hsiny, Real.sin_sq_add_cos_sq y]
  have heq9 : cos y ^ 2 = 1 / 2 := by
    have heq6 : cos y ^ 2 + sin y ^ 2 = 1 := by
      exact Real.cos_sq_add_sin_sq y
    have heq8 : ( (cos y)^2 ) * ( (sin y)^2 ) = 1 / 4 := by
      have heq7 : (cos y)^6 + (sin y)^6 = 1 / 4 := by
        nlinarith
      nlinarith [sq_nonneg (cos y ^ 2 - sin y ^ 2), sq_nonneg (cos y ^ 2 - 1 / 2), sq_nonneg (sin y ^ 2 - 1 / 2)]
    rw [show (sin y)^2 = 1 - (cos y)^2 by linarith [Real.cos_sq_add_sin_sq y]] at heq8
    nlinarith
  -- cos^2 y = 1/2, so cos y = sqrt(2)/2
  have heq13 : cos y = Real.sqrt 2 / 2 := by
    have h9 : cos y ^ 2 = 1 / 2 := heq9
    have hc : cos y > 0 := hcosy
    have h01 : cos y = Real.sqrt (1 / 2) := by
      rw [← h9]
      field_simp [hc]
    rw [h01]
    have : Real.sqrt (1 / 2) = Real.sqrt 2 / 2 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> ring_nf
      <;> norm_num
    linarith
  have heq14 : sin y = Real.sqrt 2 / 2 := by
    have h9 : sin y ^ 2 = 1 / 2 := by
      have heq6 : cos y ^ 2 + sin y ^ 2 = 1 := by
        exact Real.cos_sq_add_sin_sq y
      nlinarith [heq9]
    have hc : sin y > 0 := hsiny
    have h01 : sin y = Real.sqrt (1 / 2) := by
      rw [← h9]
      field_simp [hc]
    rw [h01]
    have : Real.sqrt (1 / 2) = Real.sqrt 2 / 2 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> ring_nf
      <;> norm_num
    linarith
  have heq15 : y = Real.pi / 4 := by
    have heq16 : sin y = Real.sqrt 2 / 2 := heq14
    have heq17 : y = Real.arcsin (sin y) := by
      rw [Real.arcsin_sin]
      all_goals
        try linarith [hy1, hy2, Real.pi_pos, Real.pi_gt_three]
    have heq18 : Real.arcsin (sin y) = Real.arcsin (Real.sqrt 2 / 2) := by
      rw [heq16]
    have heq19 : Real.arcsin (Real.sqrt 2 / 2) = Real.pi / 4 := by
      have h10 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
      have h11 : Real.arcsin (Real.sin (Real.pi / 4)) = Real.pi / 4 := by
        apply Real.arcsin_sin
        all_goals
          try linarith [Real.pi_pos, Real.pi_gt_three]
      rw [h10] at h11
      linarith
    linarith [heq17, heq18, heq19]
  have heq16 : x = Real.pi / 4 := by
    have heq17 : cos x = Real.sqrt 2 / 2 := by
      rw [heq1]
      rw [heq13]
      nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have heq18 : x = Real.arccos (cos x) := by
      rw [Real.arccos_cos]
      all_goals
        try nlinarith [Real.pi_pos, hx1, hx2, Real.pi_gt_three]
    have heq19 : Real.arccos (cos x) = Real.arccos (Real.sqrt 2 / 2) := by
      rw [heq17]
    have heq20 : Real.arccos (Real.sqrt 2 / 2) = Real.pi / 4 := by
      have h9 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
      have h21 : Real.arccos (Real.cos (Real.pi / 4)) = Real.pi / 4 := by
        apply Real.arccos_cos
        all_goals
          try nlinarith [Real.pi_pos, Real.pi_gt_three]
      rw [h9] at h21
      linarith
    linarith [heq18, heq19, heq20]
  exact ⟨heq16, heq15⟩