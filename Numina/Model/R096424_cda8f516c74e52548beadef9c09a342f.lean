import Mathlib

theorem algebra_262967 (a : ℝ) (a1 a2 a3 a4 : ℝ)
    (h : ∀ x, (x + a) ^ 4 = x ^ 4 + a1 * x ^ 3 + a2 * x ^ 2 + a3 * x + a4)
    (h' : a1 + a2 + a3 = 64) :
    a = 2 := by 
  have eqA : a1 = 4 * a := by
    have eq1 := h 1
    have eq2 := h (-1)
    have eq3 := h 2
    have eq4 := h (-2)
    have eq5 := h 0
    ring_nf at eq1 eq2 eq3 eq4 eq5
    nlinarith [sq_nonneg (a - 2), sq_nonneg (a + 2), sq_nonneg (a^2 - 4), sq_nonneg (a^2 + 4), sq_nonneg (a * a), sq_nonneg (a - 1), sq_nonneg (a + 1)]
  have eqB : a2 = 6 * a^2 := by
    have eq1 := h 1
    have eq2 := h (-1)
    have eq3 := h 2
    have eq4 := h (-2)
    have eq5 := h 0
    ring_nf at eq1 eq2 eq3 eq4 eq5
    nlinarith [sq_nonneg (a - 2), sq_nonneg (a + 2), sq_nonneg (a^2 - 4), sq_nonneg (a^2 + 4), sq_nonneg (a * a), sq_nonneg (a - 1), sq_nonneg (a + 1)]
  have eqC : a3 = 4 * a^3 := by
    have eq1 := h 1
    have eq2 := h (-1)
    have eq3 := h 2
    have eq4 := h (-2)
    have eq5 := h 0
    ring_nf at eq1 eq2 eq3 eq4 eq5
    nlinarith [sq_nonneg (a - 2), sq_nonneg (a + 2), sq_nonneg (a^2 - 4), sq_nonneg (a^2 + 4), sq_nonneg (a * a), sq_nonneg (a - 1), sq_nonneg (a + 1)]
  rw [eqA, eqB, eqC] at h'
  have h_eq : 4 * a^3 + 6 * a^2 + 4 * a - 64 = 0 := by
    nlinarith 
  have h_eq2 : (a - 2) * (4 * a^2 + 14 * a + 32) = 0 := by
    nlinarith [h_eq]
  cases' (mul_eq_zero.mp h_eq2) with h_a2 h_quad
  · -- Solve a from h_a2: a - 2 = 0
    linarith 
  · -- Show that quadratic equation is impossible
    nlinarith [sq_nonneg (a + 7/4), sq_nonneg (a^2 + (7/2)*a + 8)]