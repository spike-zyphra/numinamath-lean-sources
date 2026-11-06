import Mathlib

theorem algebra_289193 (a b : ℝ) (f : ℝ → ℝ) (hf : ∀ x, f x = a * x + b)
    (h : ∀ x, f^[7] x = 128 * x + 381) : a + b = 5 := by

  have eq1 := h 0
  simp [Function.iterate_succ_apply', hf] at eq1

  have eq2 := h 1
  simp [Function.iterate_succ_apply', hf] at eq2

  have h2 : a = 2 := by
    have h1 : a^7 = 128 := by
      nlinarith
    have h_eq : a^7 - 128 = 0 := by linarith
    have h_eq2 : (a - 2) * (a^6 + 2*a^5 + 4*a^4 + 8*a^3 + 16*a^2 + 32*a + 64) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h_eq2) with h_eq3 h_eq4
    · -- Real solution from the factor (a - 2)
      linarith
    · -- Complex polynomial factor
      nlinarith [sq_nonneg (a^3), sq_nonneg (a^2 + a), sq_nonneg (a + 1),
        sq_nonneg (a^2 + a + 1), sq_nonneg (a^2 - 2*a + 4), sq_nonneg (a^2 + 4*a + 16)]

  have ha : a = 2 := h2

  have hb : b = 3 := by
    rw [ha] at eq1
    nlinarith

  linarith [ha, hb]