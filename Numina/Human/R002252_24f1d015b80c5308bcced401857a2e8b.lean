import Mathlib
/-let f: ℝ → ℝ be a function such that
f(f(x))=(x^2-x)/2 * f(x) +2-x for all x: ℝ, find all possible values of f(2)-/
theorem algebra_77227 {f : ℝ → ℝ} (h : ∀ x, f (f x) = (x ^ 2 - x) / 2 * f x + 2 - x) :
    f 2 = 2 := by
  have eq1 := h 2
  norm_num at eq1
  have eq2 := h 0
  norm_num at eq2
  have eq3 := h (f 2)
  norm_num at eq3
  rw [eq1] at eq3
  ring_nf at eq3
  have eq4: f 2 = (f 2) ^ 3 / 2 - (f 2) ^ 2 / 2 - (f 2) + 2 := by linarith [eq3]
  -- now we see that there are only 3 cases
  have h1: (f 2 - 1) * (f 2 - 2) * (f 2 + 2) = 0 := by
    ring_nf at eq4 ⊢
    linarith
  cases' (mul_eq_zero.mp h1) with h2 h3
  cases' (mul_eq_zero.mp h2) with h4 h5
  · -- for the case f(2) = 1, we show contradiction
    have h6: f 2 = 1 := by linarith
    have eq4 := h 0
    norm_num at eq4
    have eq5 := h (f 0)
    rw [eq4] at eq5
    rw [h6] at eq5
    have h7: (f 0 - 1) ^ 2 = 0 := by
      nlinarith
    have h8: f 0 = 1 := by nlinarith
    rw [h8] at eq4
    have h9: f 1 = 2 := by linarith
    have eq6 := h 2
    norm_num at eq6
    rw [h6] at eq6
    have h10: f 1 = 1 := by linarith
    linarith [h9, h10]
  · -- for the case f(2) = 2
    linarith
  · -- for the case f(2) = -2, we show contradiction
    have h7: f 2 = -2 := by linarith
    have eq4 := h 0
    norm_num at eq4
    have eq5 := h (f 0)
    rw [eq4] at eq5
    rw [h7] at eq5
    have h8: (f 0) ^ 2 - 2 * (f 0) + 4 = 0 := by
      nlinarith
    have h9: (f 0 - 1) ^ 2 ≥ 0 := by
      apply sq_nonneg
    nlinarith