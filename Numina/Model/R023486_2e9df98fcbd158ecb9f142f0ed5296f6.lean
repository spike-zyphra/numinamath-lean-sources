import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_10946 {x : ℝ} (hx : x ∈ Ioo 0 (π/2)) (h : 6 * cos x = 5 * tan x)
  (P : ℝ × ℝ) (hP : P = (x, 6 * cos x)) (P1 : ℝ × ℝ) (hP1 : P1 = (x, 0))
  (P2 : ℝ × ℝ) (hP2 : P2 = (x, sin x)) :
  dist P1 P2 = 2/3 := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : sin x > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h2 : cos x > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]

  have h3 : cos x ≠ 0 := by linarith
  have h4 : 5 * tan x = 5 * (sin x / cos x) := by
    rw [tan_eq_sin_div_cos]
  rw [h4] at h

  have h5 : 6 * cos x ^ 2 = 5 * sin x := by
    field_simp [h3] at h ⊢
    nlinarith [Real.sin_sq_add_cos_sq x]
  have h6 : 6 * (1 - sin x ^ 2) = 5 * sin x := by
    have h7 : cos x ^ 2 = 1 - sin x ^ 2 := by
      have h8 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
      linarith
    rw [h7] at h5
    linarith

  --Solving quadratic equation
  have h7 : 6 * (sin x) ^ 2 + 5 * (sin x) - 6 = 0 := by
    nlinarith [h6]

  have h8 : sin x = 2/3 := by
    have h9 : (sin x - 2/3) * (6 * sin x + 18) = 0 := by
      nlinarith [h7, sq_nonneg (sin x)]
    cases' (mul_eq_zero.mp h9) with h10 h11
    · -- Solving first part of multiplication
      linarith
    · -- Second part of multiplication, inconsistent part
      nlinarith [Real.sin_le_one x, h1]

  rw [hP1] at *
  rw [hP2] at *
  simp [dist, h8]
  all_goals norm_num