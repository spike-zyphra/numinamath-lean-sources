import Mathlib

theorem algebra_7343 {a : ℝ} (h : ∃ b, ∀ x, x^2 - a * x + 121 = (x - b)^2) :
    a = 22 ∨ a = -22 := by
  rcases h with ⟨b, hb⟩
  have h1 := hb 0
  have h1' : b^2 = 121 := by
    nlinarith
  have hb1 : b = 11 ∨ b = -11 := by
    have h1 : b^2 = 121 := by 
      nlinarith
    have h2 : b^2 - 121 = 0 := by 
      linarith
    have h3 : (b - 11) * (b + 11) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h3) with h4 h5
    · left
      linarith
    · right
      linarith
  cases' hb1 with hb1 hb1
  · -- Case b = 11, we need to prove a = 22
    have hb_eq11 : b = 11 := hb1
    have h2 := hb 1
    rw [hb_eq11] at h2
    have ha : a = 22 := by
      nlinarith
    left
    exact ha
  · -- Case b = -11, we need to prove a = -22
    have hb_eq11 : b = -11 := hb1
    have h2 := hb 1
    rw [hb_eq11] at h2
    have ha : a = -22 := by
      nlinarith
    right
    exact ha