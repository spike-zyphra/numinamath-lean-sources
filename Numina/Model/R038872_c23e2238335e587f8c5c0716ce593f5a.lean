import Mathlib

theorem algebra_37854 {a : ℝ} (f : ℝ → ℝ) (h : ∀ x y, f x * f y - a * f (x * y) = x + y) :
    a = 1 ∨ a = -1 := by

  have h1 := h 0 0
  have eq1 : f 0 * f 0 - a * f (0 * 0) = (0 : ℝ) + (0 : ℝ) := by
    simpa using h1
  have eq2 : f 0 * f 0 - a * f 0 = 0 := by
    simp at eq1 ⊢
    linarith

  have eq3 : f 0 * (f 0 - a) = 0 := by
    linarith [eq2]

  have h2 := h 1 0
  have eq4 : f 1 * f 0 - a * f (1 * 0) = (1 : ℝ) + (0 : ℝ) := by
    simpa using h2

  have eq5 : f 1 * f 0 - a * f 0 = 1 := by
    simp at eq4 ⊢
    linarith

  have eq6 : f 0 ≠ 0 := by
    by_contra h3
    rw [h3] at eq5
    nlinarith

  have eq7 : a = f 0 := by
    apply (mul_left_inj' eq6).mp
    linarith [eq3]

  have eq8 : f 0 = a := by linarith [eq7]

  -- Substituting x = 1, y = 0: f(1)f(0) - a f(0) = 1

  have eq9 : f 0 * (f 1 - a) = 1 := by
    linarith [eq5, eq7]

  have eq10 := h 1 1
  have eq11 : f 1 * f 1 - a * f (1 * 1) = (1 : ℝ) + (1 : ℝ) := by
    simpa using eq10

  have eq12 : f 1 * f 1 - a * f 1 = 2 := by
    simp at eq11 ⊢
    linarith

  have eq13 : a ≠ 0 := by
    by_contra h4
    have h5 : a = 0 := by linarith [h4]
    rw [h5] at eq9
    rw [eq8] at eq9
    nlinarith [eq6]

  have eq14 : f 1 = a + 1 / a := by
    have h6 : a * (f 1 - a) = 1 := by
      rw [eq8] at eq9
      linarith
    field_simp [eq13] at *
    linarith

  rw [eq14] at eq12

  have eq15 : a ^ 2 = 1 := by
    field_simp [eq13] at eq12
    nlinarith [sq_nonneg (a ^ 2), sq_nonneg (a + 1), sq_nonneg (a - 1)]

  have eq16 : a = 1 ∨ a = -1 := by
    rw [sq_eq_one_iff] at eq15
    tauto

  exact eq16