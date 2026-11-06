import Mathlib

theorem algebra_120545 {a b : ℝ} (ha : a ≠ -1) (hb : b ≠ -1) (h : a / (1 + b) + b / (1 + a) = 1) :
    a ^ 3 + b ^ 3 = a + b := by
  have h1 : a * (1 + a) + b * (1 + b) = (1 + b) * (1 + a) := by
    have hne1 : (1 + b) ≠ 0 := by
      intro h'
      apply hb
      linarith
    have hne2 : (1 + a) ≠ 0 := by
      intro h'
      apply ha
      linarith
    field_simp [hne1, hne2] at h ⊢
    linarith
  have h2 : a ^ 2 - a * b + b ^ 2 = 1 := by
    nlinarith [h1]

  have h3 : a ^ 3 + b ^ 3 = (a + b) * (a ^ 2 - a * b + b ^ 2) := by
    ring

  rw [h3, h2]
  all_goals ring