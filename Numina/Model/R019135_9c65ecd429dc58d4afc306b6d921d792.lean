import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_314333 (m : ℝ) :
  (∀ x : ℝ, x^2 - 3 * x + 4 ≠ 0 → (x^2 - m * x - 2) / (x^2 - 3 * x + 4) > -1) ↔
  m ∈ Ioo (-7) 1 :=
  by
  constructor
  · -- Forward direction: if the inequality holds for all x, then m ∈ (-7, 1)
    intro h
    have h1 := h 1 (by norm_num)
    have h2 := h (-1) (by norm_num)
    have h3 : m < 1 := by
      norm_num at h1
      nlinarith
    have h4 : m > -7 := by
      norm_num at h2
      nlinarith
    exact ⟨by linarith, by linarith⟩
  · -- Backward direction: if m ∈ (-7, 1), then the inequality holds for all x
    rintro ⟨h1, h2⟩
    intro x hx
    have h_pos : x^2 - 3 * x + 4 > 0 := by
      nlinarith [sq_nonneg (x - 3 / 2)]
    have h4 : (x^2 - m * x - 2) / (x^2 - 3 * x + 4) > -1 := by
      have h5 : x^2 - 3 * x + 4 > 0 := h_pos
      apply (lt_div_iff₀ h5).mpr
      nlinarith [sq_nonneg (x * 2 - (m + 3)), sq_nonneg (x - (m + 3) / 4), sq_nonneg (m + 3), sq_nonneg (x - 2), sq_nonneg (x - (m)), sq_nonneg (x * 2 - (m + 3) * 2), sq_nonneg (x - (-7 : ℝ)), sq_nonneg (x - (1 : ℝ)), mul_pos (show (0 : ℝ) < 4 by norm_num) (show (0 : ℝ) < 4 by norm_num)]
    exact h4