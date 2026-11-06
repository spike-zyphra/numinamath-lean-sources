import Mathlib

open Real Set
open scoped Real

theorem algebra_143502 (α : ℝ) (hα : α ∈ Ioo (π/2) π) (h : sin (2*α) = -sin α) :
    cot α = -sqrt 3 / 3 := by
  rw [mem_Ioo] at hα
  have h1 : sin α > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [hα.left, hα.right]
    linarith [hα.left, hα.right]
  have h2 : sin (2 * α) = 2 * sin α * cos α := by
    rw [sin_two_mul]
  rw [h2] at h
  have h3 : sin α ≠ 0 := by nlinarith
  have h4 : 2 * cos α = -1 := by
    apply (mul_left_inj' h3).mp
    linarith
  have hcos : cos α = -1 / 2 := by linarith
  have h4 : sin α = Real.sqrt 3 / 2 := by
    have h5 : sin α ^ 2 + cos α ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq α
    rw [hcos] at h5
    have h6 : sin α ^ 2 = 3 / 4 := by nlinarith
    have h7 : sin α = Real.sqrt (3 / 4) := by
      have h8 : sin α > 0 := h1
      have h9 : sin α ^ 2 - 3 / 4 = 0 := by linarith
      have h10 : (sin α - Real.sqrt (3 / 4)) * (sin α + Real.sqrt (3 / 4)) = 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (3 / 4 : ℝ) > 0 by norm_num : (3 / 4 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 / 4 : ℝ) by norm_num : (0 : ℝ) ≤ (3 / 4 : ℝ))]
      cases' (mul_eq_zero.mp h10) with h11 h12
      · -- sin α - Real.sqrt (3 / 4) = 0
        linarith
      · -- sin α + Real.sqrt (3 / 4) = 0
        have h13 : Real.sqrt (3 / 4) > 0 := by positivity
        nlinarith [Real.sqrt_pos.mpr (show (3 / 4 : ℝ) > 0 by norm_num : (3 / 4 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 / 4 : ℝ) by norm_num : (0 : ℝ) ≤ (3 / 4 : ℝ)), Real.sqrt_pos.mpr (show (3 / 4 : ℝ) > 0 by norm_num : (3 / 4 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 / 4 : ℝ) by norm_num : (0 : ℝ) ≤ (3 / 4 : ℝ))]
    have h8 : Real.sqrt (3 / 4) = Real.sqrt 3 / 2 := by
      calc
        Real.sqrt (3 / 4) = Real.sqrt (3 / 4) := by rfl
        _ = Real.sqrt (3) / Real.sqrt (4) := by
          rw [Real.sqrt_div]
          all_goals linarith
        _ = Real.sqrt (3) / 2 := by
          have h5 : Real.sqrt (4 : ℝ) = 2 := by
            rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
          rw [h5]
    rw [h8] at h7
    linarith
  have h3 : cot α = cos α / sin α := by
    rw [cot_eq_cos_div_sin]
  rw [h3]
  rw [hcos, h4]
  field_simp
  <;> ring_nf <;> rw [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ))] <;> ring_nf <;> norm_num
  <;> ring