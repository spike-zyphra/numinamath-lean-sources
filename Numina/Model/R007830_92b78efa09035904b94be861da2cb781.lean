import Mathlib

open Real Set
open scoped Real

theorem calculus_23471 (x : ℝ) (hx : x ∈ Ioo 0 Real.pi) (h : sin x + cos x = 1 / 5) :
    tan x = -4 / 3 := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : sin x + cos x = 1 / 5 := h
  have h2 : (sin x) ^ 2 + (cos x) ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have h3 : (sin x + cos x) ^ 2 = (1 / 5) ^ 2 := by
    rw [h]
  have h4 : (sin x + cos x) ^ 2 = (sin x) ^ 2 + (cos x) ^ 2 + 2 * (sin x * cos x) := by ring
  have h5 : (sin x) * (cos x) = -12 / 25 := by
    nlinarith
  have h9 : sin x ≥ 0 := by
    apply sin_nonneg_of_nonneg_of_le_pi
    linarith
    linarith [Real.pi_gt_three]
  have h6 : sin x = 4 / 5 ∨ sin x = -3 / 5 := by
    have h10 : (sin x - 4 / 5) * (sin x + 3 / 5) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h10) with h11 h12
    · -- sin x - 4/5 = 0, so sin x = 4/5
      left
      nlinarith
    · -- sin x + 3/5 = 0, so sin x = -3/5
      right
      nlinarith
  cases' h6 with h10 h12
  · -- sin x = 4/5
    have h11 : cos x = -3 / 5 := by
      nlinarith
    rw [tan_eq_sin_div_cos]
    rw [h11, h10]
    all_goals norm_num
  · -- sin x = -3/5, contradicting sin x ≥ 0
    have h11 : sin x < 0 := by
      nlinarith
    linarith