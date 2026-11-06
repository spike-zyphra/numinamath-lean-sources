import Mathlib

theorem algebra_190695 {a b c : ℝ} (ha : a^2 * (b + c) = 2008) (hb : b^2 * (a + c) = 2008) (hab : a ≠ b) :
    c^2 * (a + b) = 2008 := by
  have h1 : a ^ 2 * (b + c) - b ^ 2 * (a + c) = 0 := by
    linarith
  have eq1 : (a - b) * (a * b + c * (a + b)) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp eq1) with h2 h3
  · -- When `a - b = 0` ...
    exfalso
    exact hab (by linarith)
  · -- When `ab + c * (a + b) = 0` ...
    have eq2 : a * b + c * (a + b) = 0 := by
      nlinarith
    have eq3 : a * b = -c * (a + b) := by 
      nlinarith
    have eq4 : a^2 * (b + c) + b^2 * (a + c) = 4016 := by
      nlinarith
    have eq5 : a * b * (a + b) + c * (a^2 + b^2) = 4016 := by
      nlinarith [eq4]
    have eq6 : a * b * c = -2008 := by
      have eq7 : a * b * (a + b) + c * (a^2 + b^2) = 4016 := by 
        nlinarith [eq4]
      rw [show a * b = -c * (a + b) by linarith [eq3]] at eq7
      nlinarith [sq_pos_of_ne_zero (sub_ne_zero_of_ne hab), sq_pos_of_ne_zero (show a - b ≠ 0 by
        intro h
        apply hab
        linarith
      ), sq_nonneg (a + b), sq_nonneg (c)]
    have eq7 : c^2 * (a + b) = 2008 := by
      have eq8 : a * b * c = -c^2 * (a + b) := by 
        have h1 : a * b = -c * (a + b) := eq3
        calc 
          a * b * c = (a * b) * c := by ring
          _ = (-c * (a + b)) * c := by rw [h1]
          _ = -c^2 * (a + b) := by ring
      nlinarith [eq6, eq8, sq_nonneg (a + b), sq_nonneg (c)]
    exact_mod_cast eq7