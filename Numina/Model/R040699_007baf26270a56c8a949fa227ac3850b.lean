import Mathlib

theorem algebra_14890 {a b : ℤ} (h : ∀ y : ℤ, (3 * y + a) * (y + b) = 3 * y ^ 2 - y - 24) :
    a - b = 11 := by
  have eq1 := h 0
  have eq2 := h 1
  have eq3 := h 2
  have eq4 := h 3
  have eq5 : a * b = -24 := by
    nlinarith
  have eq6 : 3 * b + a = -1 := by
    nlinarith [eq1, eq2]
  have h1 : b = -3 := by
    have h2 : a = -1 - 3 * b := by linarith
    rw [h2] at eq5
    have h3 : 3 * b ^ 2 + b - 24 = 0 := by
      nlinarith
    have h4 : (b + 3) * (3 * b - 8) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h4) with h5 h6
    · -- b + 3 = 0
      linarith
    · -- 3 * b - 8 = 0
      exfalso
      omega
  have h2 : a = 8 := by
    rw [h1] at eq6
    linarith
  rw [h2, h1]
  all_goals norm_num