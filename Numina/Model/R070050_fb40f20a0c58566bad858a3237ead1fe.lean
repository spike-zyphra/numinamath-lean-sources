import Mathlib

open Real Set
open scoped Real

theorem algebra_307621 {x : ℝ} (hx : x ∈ Ico 0 Real.pi) (h : sin x + cos x = 1 / 5) :
    tan x = -4 / 3 := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have h2 : sin x + cos x = 1 / 5 := h
  have h3 : sin x * cos x = -12 / 25 := by
    have h4 : (sin x + cos x) ^ 2 = (1 / 5) ^ 2 := by
      rw [h2]
    have h5 : (sin x + cos x) ^ 2 = sin x ^ 2 + cos x ^ 2 + 2 * (sin x * cos x) := by ring
    rw [h5] at h4
    nlinarith [h1]
  have h5 : sin x ≥ 0 := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    linarith
    linarith [show x ≤ Real.pi by linarith [hx2]]
  have h4 : sin x = 4 / 5 := by
    nlinarith [sq_nonneg (sin x - 4 / 5), sq_nonneg (sin x + 3 / 5), sq_nonneg (cos x + 3 / 5), sq_nonneg (cos x - 4 / 5), h2, h1, h5]
  have h5 : cos x = -3 / 5 := by
    nlinarith [h2, h4, h1]
  rw [Real.tan_eq_sin_div_cos]
  rw [h4, h5]
  norm_num
  <;> nlinarith