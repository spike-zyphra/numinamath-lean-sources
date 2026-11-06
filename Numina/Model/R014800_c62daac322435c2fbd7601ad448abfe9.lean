import Mathlib

theorem algebra_153735 {f : ℝ → ℝ} (hf : ∀ x, 0 < f x)
    (h : ∀ x1 x2, f (x1 + x2) = 2 * f x1 * f x2) (h2 : f 2 = 2) :
    f 1 = 0.5 * 2 ^ 1 ∧ f 0 = 0.5 * 2 ^ 0 ∧ f 3 = 0.5 * 2 ^ 3 ∧ f 6 = 0.5 * 2 ^ 6 := by

  have eq1 : f 1 = 1 := by
    have h1 : f (1 + 1) = 2 * f 1 * f 1 := h 1 1
    have eq2 : f (1 + 1) = f 2 := by norm_num
    rw [eq2] at h1
    rw [h2] at h1
    have hf1 : 0 < f 1 := hf 1
    have eq3 : (f 1 : ℝ) ^ 2 = 1 := by
      nlinarith
    have eq4 : f 1 = 1 := by
      nlinarith [sq_nonneg (f 1), hf1]
    exact eq4
  have eq2 : f 0 = (1 / 2 : ℝ) := by
    have h0 : f (0 + 0) = 2 * f 0 * f 0 := h 0 0
    have eq3 : f (0 + 0) = f 0 := by norm_num
    rw [eq3] at h0
    have hf0 : 0 < f 0 := hf 0
    have eq4 : f 0 * (2 * f 0 - 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp eq4) with eq5 eq6
    · -- f 0 = 0
      linarith [hf0, eq5]
    · -- 2 * f 0 - 1 = 0
      linarith
  have eq3 : f 3 = 4 := by
    have h3 : f (2 + 1) = 2 * f 2 * f 1 := h 2 1
    have eq4 : f (2 + 1) = f 3 := by norm_num
    rw [eq4] at h3
    rw [h2, eq1] at h3
    nlinarith
  have eq4 : f 6 = 32 := by
    have h6 : f (3 + 3) = 2 * f 3 * f 3 := h 3 3
    have eq5 : f (3 + 3) = f 6 := by norm_num
    rw [eq5] at h6
    rw [eq3] at h6
    nlinarith
  constructor
  · -- f(1) = 0.5 * 2 ^ 1
    rw [eq1]
    norm_num
  constructor
  · -- f(0) = 0.5 * 2 ^ 0
    rw [eq2]
    norm_num
  constructor
  · -- f(3) = 0.5 * 2 ^ 3
    rw [eq3]
    norm_num
  · -- f(6) = 0.5 * 2 ^ 6
    rw [eq4]
    norm_num