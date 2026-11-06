import Mathlib

theorem algebra_187806 (d v : ℝ) (h₀ : d > 0) (h₁ : v > 0)
    (h₂ : d / v = d / (v + w) + 3 / 60) (h₃ : d / w = d / (v + w) - 3 / 60)
    (h₄ : d / (v + w) = 15 / 60) :
    w / v = 2 := by 
  have h₅ : v + w ≠ 0 := by
    by_contra h
    have h₆ : v + w = 0 := by linarith
    have h₇ : d / (v + w) = 0 := by
      rw [h₆]
      norm_num
      all_goals nlinarith
    linarith [h₄, h₇, h₀]

  have eq1 : d / v = 18 / 60 := by 
    have eq2 : d / v = d / (v + w) + 3 / 60 := h₂
    rw [show d / (v + w) = 15 / 60 by linarith [h₄]] at eq2
    linarith
  have eq2 : d / w = 12 / 60 := by 
    have eq3 : d / w = d / (v + w) - 3 / 60 := h₃
    rw [show d / (v + w) = 15 / 60 by linarith [h₄]] at eq3
    linarith

  have h6 : d = 18 / 60 * v := by
    have h8 : d / v = 18 / 60 := eq1
    have : v ≠ 0 := by nlinarith
    field_simp at h8 ⊢
    linarith
  have h7 : d = 12 / 60 * w := by
    have h8 : d / w = 12 / 60 := eq2
    have : w ≠ 0 := by
      by_contra h
      rw [h] at h₃
      norm_num at h₃
      all_goals nlinarith [h₀, h₁, h₄]
    field_simp at h8 ⊢
    linarith
  have h10 : 3 * v = 2 * w := by
    nlinarith [h6, h7]

  have h12 : w / v = 2 := by 
    have h8 : d = 18 / 60 * v := h6
    have h9 : d = 12 / 60 * w := h7
    have h10' : 3 * v = 2 * w := h10
    have hv : v ≠ 0 := by nlinarith
    have hw : w ≠ 0 := by 
      by_contra h
      rw [h] at h₃
      norm_num at h₃
      all_goals nlinarith [h₀, h₁, h₄]
    field_simp at *
    nlinarith [h₀, h₁, h6, h7, h10, h₀, h₁, h₄, hv, hw]

  linarith [h12]