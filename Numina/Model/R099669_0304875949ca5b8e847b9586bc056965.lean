import Mathlib

theorem algebra_218385 {x : Fin 3 → ℝ} (h1 : 2 * (x 0)^2 / (1 + (x 0)^2) = x 1)
    (h2 : 2 * (x 1)^2 / (1 + (x 1)^2) = x 2) (h3 : 2 * (x 2)^2 / (1 + (x 2)^2) = x 0) :
    (x = ![0, 0, 0] ∨ x = ![1, 1, 1]) := by
  have h4 : x 0^3 - 2 * x 0^2 + x 0 = 0 := by
    have h1' : 2 * (x 0)^2 / (1 + (x 0)^2) = x 1 := h1
    have h2' : 2 * (x 1)^2 / (1 + (x 1)^2) = x 2 := h2
    have h3' : 2 * (x 2)^2 / (1 + (x 2)^2) = x 0 := h3
    field_simp [show 1 + (x 0)^2 ≠ 0 by positivity] at h1'
    field_simp [show 1 + (x 1)^2 ≠ 0 by positivity] at h2'
    field_simp [show 1 + (x 2)^2 ≠ 0 by positivity] at h3'
    nlinarith [sq_nonneg (x 0 - 1), sq_nonneg (x 1 - 1), sq_nonneg (x 2 - 1),
              sq_nonneg (x 1 - x 0), sq_nonneg (x 2 - x 1), sq_nonneg (x 2 - x 0)]
  have h5 : x 0 * (x 0 - 1)^2 = 0 := by
    ring_nf at h4 ⊢
    linarith
  cases (mul_eq_zero.mp h5) with
  | inl h6 =>
    left
    have hx0 : x 0 = 0 := h6
    have hx1 : x 1 = 0 := by
      rw [hx0] at h1
      norm_num at h1 ⊢
      linarith
    have hx2 : x 2 = 0 := by
      rw [hx1] at h2
      norm_num at h2 ⊢
      linarith
    ext i
    fin_cases i
    · simp [hx0]
    · simp [hx1]
    · simp [hx2]
  | inr h7 =>
    right
    have hx0 : x 0 = 1 := by
      nlinarith
    have hx1 : x 1 = 1 := by
      rw [hx0] at h1
      norm_num at h1 ⊢
      linarith
    have hx2 : x 2 = 1 := by
      rw [hx1] at h2
      norm_num at h2 ⊢
      linarith
    ext i
    fin_cases i
    · simp [hx0]
    · simp [hx1]
    · simp [hx2]