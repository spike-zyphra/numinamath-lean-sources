import Mathlib

theorem algebra_274035 (d v : ℝ) (h₀ : d > 0) (h₁ : v > 0)
    (h₂ : d / (v + 20) = d / v - 2 / 60) (h₃ : d / (v - 20) = d / v + 3 / 60) :
    d = 20 := by

  have h₄ : v + 20 ≠ 0 := by
    linarith
  have h₅ : v ≠ 0 := by
    linarith
  have h₆ : v - 20 ≠ 0 := by
    by_contra h
    have h₇ : v = 20 := by
      linarith
    rw [h₇] at h₃
    field_simp [(show (20 : ℝ) - 20 = 0 by norm_num : (20 : ℝ) - 20 = 0)] at h₃
    all_goals
      nlinarith
  have eq1 : d * v = d * (v + 20) - (2 / 60) * (v) * (v + 20) := by
    have h4 : v + 20 ≠ 0 := h₄
    have h5 : v ≠ 0 := h₅
    field_simp [h4, h5] at h₂
    ring_nf at h₂ ⊢
    nlinarith
  have eq2 : d * v = d * (v - 20) + (3 / 60) * (v) * (v - 20) := by
    have h9 : v - 20 ≠ 0 := h₆
    have h10 : v ≠ 0 := h₅
    field_simp [h9, h10] at h₃
    ring_nf at h₃ ⊢
    nlinarith
  have h8 : 600 * d = v * (v + 20) := by
    nlinarith
  have h9 : 400 * d = v * (v - 20) := by
    nlinarith
  have h10 : v = 5 * d := by
    nlinarith
  rw [h10] at h8
  have h11 : d * (d - 20) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h11) with h12 h13
  · 
    nlinarith
  · 
    linarith