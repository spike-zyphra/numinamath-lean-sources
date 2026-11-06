import Mathlib

theorem algebra_214768 {a b : ℝ} (x : ℕ → ℝ) (h : ∀ n, x (n + 1) = x n - x (n - 1))
    (hx1 : x 1 = a) (hx2 : x 2 = b) :
    x 100 = -a ∧ ∑ i in Finset.Icc 1 100, x i = 2 * b - a := by

  have h1 := h 0
  simp at h1

  have ha0 : a = 0 := by
    linarith [hx1, h1]

  have h2 := h 1
  norm_num at h2

  have h3 : b = -x 0 := by
    have h4 : x 2 = x 1 - x 0 := by linarith
    rw [hx2] at h4
    rw [show x 1 = (0 : ℝ) by linarith [h1]] at h4
    linarith

  have hx100 : x 100 = -a := by
    have h100 : x 100 = 0 := by
      norm_num [h] at *
      all_goals
        linarith
    rw [h100]
    linarith [ha0]

  have h5 : ∑ i in Finset.Icc 1 100, x i = 2 * b - a := by
    norm_num [Finset.sum_Icc_succ_top, h, ha0, h3] at *
    all_goals
      linarith

  constructor
  · exact hx100
  · exact h5