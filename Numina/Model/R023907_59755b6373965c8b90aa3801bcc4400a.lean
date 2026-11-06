import Mathlib


lemma lemma_1 {a b : ℝ} (h : a / (1 + a) + b / (1 + b) = 1) : a * b = 1 := by
  have h1 : (1 + a) ≠ 0 := by
    by_contra h_eq
    have h_eq1 : a = -1 := by linarith
    have h_eq2 : (1 + a) = 0 := by linarith
    have eq_zero : a / (1 + a) = 0 := by
      rw [h_eq1]
      norm_num
    have hb_eq : b / (1 + b) = 1 := by linarith [h, eq_zero]
    by_cases hb : 1 + b = 0
    · 
      have hb_eq1 : b = -1 := by linarith
      rw [hb_eq1] at hb_eq
      norm_num at hb_eq
    · 
      field_simp [hb] at hb_eq
  have h2 : (1 + b) ≠ 0 := by
    by_contra h_eq
    have h_eq1 : b = -1 := by linarith
    have h_eq2 : (1 + b) = 0 := by linarith
    have eq_zero : b / (1 + b) = 0 := by
      rw [h_eq1]
      norm_num
    have ha_eq : a / (1 + a) = 1 := by linarith [h, eq_zero]
    by_cases ha : 1 + a = 0
    · 
      have ha_eq1 : a = -1 := by linarith
      rw [ha_eq1] at ha_eq
      norm_num at ha_eq
    · 
      field_simp [ha] at ha_eq
  have eq1 : a * (1 + b) + b * (1 + a) = (1 + a) * (1 + b) := by
    have eq2 : a / (1 + a) + b / (1 + b) = 1 := h
    have eq3 : a / (1 + a) + b / (1 + b) = (a * (1 + b) + b * (1 + a)) / ((1 + a) * (1 + b)) := by
      field_simp [h1, h2]
      <;> ring
    rw [eq3] at eq2
    have eq4 : (a * (1 + b) + b * (1 + a)) / ((1 + a) * (1 + b)) = 1 := eq2
    have eq5 : a * (1 + b) + b * (1 + a) = (1 + a) * (1 + b) := by
      field_simp [h1, h2] at eq4 ⊢
      all_goals linarith
    linarith
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a * b - 1)]


theorem algebra_142041 {a b : ℝ} (h : a / (1 + a) + b / (1 + b) = 1) :
    a / (1 + b ^ 2) - b / (1 + a ^ 2) = a - b := by
  have h1 : a * b = 1 := lemma_1 h
  have eq1 : a / (1 + b ^ 2) - b / (1 + a ^ 2) = (a * (1 + a ^ 2) - b * (1 + b ^ 2)) / ((1 + b ^ 2) * (1 + a ^ 2)) := by 
    field_simp [(show (1 + b^2) ≠ 0 by 
      by_contra h_eq
      have : b^2 = -1 := by nlinarith
      have : b^2 ≥ 0 := sq_nonneg b
      nlinarith
    ), (show (1 + a^2) ≠ 0 by 
      by_contra h_eq
      have : a^2 = -1 := by nlinarith
      have : a^2 ≥ 0 := sq_nonneg a
      nlinarith
    )]
    ring
  have eq2 : a * (1 + a ^ 2) - b * (1 + b ^ 2) = (a - b) * (2 + a^2 + b^2) := by
    have h2 : a * b = 1 := h1
    have eq3 : a * (1 + a ^ 2) - b * (1 + b ^ 2) = (a - b) + (a^3 - b^3) := by 
      nlinarith
    have eq4 : a^3 - b^3 = (a - b) * (a^2 + a * b + b^2) := by 
      ring_nf
    rw [eq3, eq4]
    have h3 : a * b = 1 := h1
    have h4 : a^2 + a * b + b^2 = a^2 + 1 + b^2 := by
      rw [show a * b = 1 by linarith]
    rw [h4]
    ring_nf
  have eq3 : (1 + b^2) * (1 + a^2) = 2 + a^2 + b^2 := by
    have h2 : a * b = 1 := h1
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a + b), sq_nonneg (a - b)]
  rw [eq1, eq2, eq3]
  have h2 : (2 + a ^ 2 + b ^ 2) ≠ 0 := by 
    by_contra h_eq
    have : a^2 + b^2 = -2 := by nlinarith
    have : a^2 ≥ 0 := sq_nonneg a
    have : b^2 ≥ 0 := sq_nonneg b
    nlinarith
  field_simp [h2]