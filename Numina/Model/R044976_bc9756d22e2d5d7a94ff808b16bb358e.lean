import Mathlib

open Real Set
open scoped Real

theorem calculus_15123 {θ : ℝ} {a b : ℝ} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (ha : a ≠ -b) (h : sin θ ^ 4 / a + cos θ ^ 4 / b = 1 / (a + b)) :
    sin θ ^ 8 / a ^ 3 + cos θ ^ 8 / b ^ 3 = 1 / (a + b) ^ 3 := by
  have h1 : a + b ≠ 0 := by
    intro h2
    have : a = -b := by linarith
    contradiction

  have eq1 : b * (a + b) * sin θ ^ 4 + a * (a + b) * cos θ ^ 4 = a * b := by
    have eq2 : sin θ ^ 4 / a + cos θ ^ 4 / b = 1 / (a + b) := h
    have eq3 : a ≠ 0 := ha0
    have eq4 : b ≠ 0 := hb0
    have eq5 : a + b ≠ 0 := h1

    have eq6 : sin θ ^ 4 / a + cos θ ^ 4 / b - 1 / (a + b) = 0 := by linarith

    have eq7 : (sin θ ^ 4 / a + cos θ ^ 4 / b - 1 / (a + b)) * (a * b * (a + b)) = 0 := by
      rw [eq6]
      norm_num

    have eq8 : (sin θ ^ 4 / a + cos θ ^ 4 / b - 1 / (a + b)) * (a * b * (a + b)) =
        b * (a + b) * sin θ ^ 4 + a * (a + b) * cos θ ^ 4 - a * b := by
      field_simp [ha0, hb0, h1]
      all_goals
        ring

    rw [eq8] at eq7
    linarith

  have eq2 : sin θ ^ 2 = a / (a + b) := by
    have eq3 : sin θ ^ 2 + cos θ ^ 2 = 1 := by exact Real.sin_sq_add_cos_sq θ
    have eq4 : b * (a + b) * sin θ ^ 4 + a * (a + b) * cos θ ^ 4 = a * b := eq1
    have eq5 : cos θ ^ 2 = 1 - sin θ ^ 2 := by linarith
    rw [show cos θ ^ 4 = (cos θ ^ 2) ^ 2 by ring, eq5] at eq4
    have eq6 : ((a + b) * sin θ ^ 2 - a) ^ 2 = 0 := by
      nlinarith [sq_pos_of_ne_zero (show a + b ≠ 0 by exact h1), sq_nonneg (sin θ ^ 2 - a / (a + b)), sq_nonneg (sin θ ^ 2 - a / (a + b))]
    have eq7 : (a + b) * sin θ ^ 2 - a = 0 := by
      apply pow_eq_zero 
      exact eq6
    have eq8 : sin θ ^ 2 = a / (a + b) := by 
      field_simp [show a + b ≠ 0 by exact h1] at *
      linarith
    exact eq8

  have eq3 : cos θ ^ 2 = b / (a + b) := by
    have h2 : sin θ ^ 2 + cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
    have h3 : sin θ ^ 2 = a / (a + b) := eq2
    have h4 : cos θ ^ 2 = 1 - sin θ ^ 2 := by linarith
    rw [h3] at h4
    field_simp [show a + b ≠ 0 by exact h1] at h4 ⊢
    linarith

  have eq4 : sin θ ^ 8 = (sin θ ^ 2) ^ 4 := by ring
  have eq5 : cos θ ^ 8 = (cos θ ^ 2) ^ 4 := by ring

  rw [eq4, eq5, eq2, eq3]

  field_simp [ha0, hb0, h1]
  all_goals
    ring