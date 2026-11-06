import Mathlib

theorem algebra_13830 {a h k : ℝ} : (∀ x, 3 * x ^ 2 - 6 * x - 2 = a * (x - h) ^ 2 + k) → 
a + h + k = -1 := by 
  intro h_eq
  have eq1 := h_eq 0
  have eq2 := h_eq 1
  have eq3 := h_eq 2
  ring_nf at eq1 eq2 eq3 
  have eq4 : -3 = a * (1 - 2 * h) := by 
    nlinarith 
  have eq5 : a * (4 - 4 * h) = 0 := by
    nlinarith [sq_nonneg (h - 1), sq_nonneg (h - 2), sq_nonneg (h)]
  cases' (mul_eq_zero.mp eq5) with ha h_eq
  · -- Consider case a = 0
    have hk : k = -2 := by 
      nlinarith
    have : -5 = a * (1 - h) ^ 2 + k := by
      linarith
    rw [ha, hk] at this
    nlinarith
  · -- Case where 4 - 4*h = 0, so h = 1
    have hh : h = 1 := by
      linarith
    have ha : a = 3 := by 
      rw [hh] at eq4 
      nlinarith 
    have hk : k = -5 := by
      rw [ha, hh] at eq1
      nlinarith
    linarith [ha, hk, hh]